/*
 * Copyright (c) 2026, Oracle and/or its affiliates. All rights reserved.
 * DO NOT ALTER OR REMOVE COPYRIGHT NOTICES OR THIS FILE HEADER.
 *
 * This code is free software; you can redistribute it and/or modify it
 * under the terms of the GNU General Public License version 2 only, as
 * published by the Free Software Foundation.
 *
 * This code is distributed in the hope that it will be useful, but WITHOUT
 * ANY WARRANTY; without even the implied warranty of MERCHANTABILITY or
 * FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
 * version 2 for more details (a copy is included in the LICENSE file that
 * accompanied this code).
 *
 * You should have received a copy of the GNU General Public License version
 * 2 along with this work; if not, write to the Free Software Foundation,
 * Inc., 51 Franklin St, Fifth Floor, Boston, MA 02110-1301 USA.
 *
 * Please contact Oracle, 500 Oracle Parkway, Redwood Shores, CA 94065 USA
 * or visit www.oracle.com if you need additional information or have any
 * questions.
 *
 */

#include "ci/ciInstanceKlass.hpp"
#include "ci/ciMethod.hpp"
#include "ci/ciObject.hpp"
#include "ci/ciStreams.hpp"
#include "interpreter/bytecodes.hpp"
#include "memory/allocation.hpp"
#include "memory/resourceArea.hpp"
#include "opto/c2_globals.hpp"
#include "opto/callnode.hpp"
#include "opto/compile.hpp"
#include "opto/parse.hpp"
#include "opto/phaseX.hpp"
#include "opto/trivialinlining.hpp"
#include "opto/type.hpp"
#include "prims/methodHandles.hpp"
#include "runtime/deoptimization.hpp"
#include "runtime/globals.hpp"
#include "runtime/thread.hpp"
#include "utilities/globalDefinitions.hpp"
#include "utilities/growableArray.hpp"
#include "utilities/pair.hpp"

#include <cstring>

bool BCTrivialAnalyzer::is_trivial(ciMethod* callee, JVMState* caller_state) {
  if (!InlineTrivialMethods || InlineTree::check_can_parse(callee) != nullptr) {
    return false;
  }

  ResourceMark rm;
  Compile* C = Compile::current();
  BCTrivialAnalyzer analyzer(C);

  MethodState* initial_state = analyzer.prepare_initial_state(callee, caller_state);
  if (initial_state == nullptr) {
    // The invocation will be cut off before actually invoking callee due to incompatible receiver,
    // no need to inline since the call is dead
    return false;
  }

  analyzer._call_stack.push(initial_state);
  while (analyzer._call_stack.is_nonempty()) {
    MethodState* cur_state = analyzer._call_stack.top();
    ciMethod* cur_method = cur_state->method;
    ciBytecodeStream parser(cur_method);
    parser.reset_to_bci(cur_state->bci);

    while (true) {
      parser.next();

      // A method is not trivial if there is a loop
      int bci = parser.cur_bci();
      if (cur_state->visited_bci.test_set(bci)) {
        return false;
      }

      assert(analyzer._num_nodes <= TrivialMethodNodeLimit, "must bail out already");
      Action act = analyzer.do_one_bytecode(parser);
      if (act == Action::CUTOFF) {
        return true;
      } else if (act == Action::NOT_TRIVIAL || analyzer._num_nodes > TrivialMethodNodeLimit) {
        return false;
      } else if (act == Action::RETURN || act == Action::CALL) {
        break;
      }
    }
  }

  return true;
}

BCTrivialAnalyzer::MethodState* BCTrivialAnalyzer::prepare_initial_state(ciMethod* callee, JVMState* caller_state) {
  PhaseGVN& gvn = *C->initial_gvn();
  MethodState* initial_state = new MethodState(callee);

  // This array is to detect arguments that appear multiple times
  GrowableArray<Pair<Value, Node*>> argument_tracker;
  if (!callee->is_static()) {
    Node* receiver_node = caller_state->map()->argument(caller_state, 0);
    const TypePtr* receiver_type = gvn.type(receiver_node)->is_ptr()->remove_speculative();
    const TypeOopPtr* callee_receiver_type = TypeOopPtr::make_from_klass(callee->holder());
    receiver_type = receiver_type->join(TypePtr::NOTNULL)->join(callee_receiver_type)->is_ptr();
    if (receiver_type->empty()) {
      // Indicate that the invocation will be cut off before actually invoking callee
      return nullptr;
    }

    Value receiver_value = make_value(receiver_type);
    initial_state->local.at_put_grow(0, receiver_value);
    argument_tracker.append(Pair<Value, Node*>(receiver_value, receiver_node));
  }

  int arg_start = callee->is_static() ? 0 : 1;
  for (int arg_idx_logical = 0, arg_idx_vm = arg_start; arg_idx_vm < callee->arg_size(); arg_idx_logical++) {
    Node* arg_node = caller_state->map()->argument(caller_state, arg_idx_vm);
    ciType* parm_type = callee->signature()->type_at(arg_idx_logical);

    bool found = false;
    for (const auto& p : argument_tracker) {
      if (arg_node == p.second) {
        initial_state->local.at_put_grow(arg_idx_vm, p.first);
        arg_idx_vm += parm_type->size();
        found = true;
        break;
      }
    }
    if (found) {
      continue;
    }

    const Type* arg_type = gvn.type(arg_node)->remove_speculative();
    verify_type(arg_type, parm_type);

    Value arg_value = make_value(arg_type);
    argument_tracker.append(Pair<Value, Node*>(arg_value, arg_node));
    initial_state->local.at_put_grow(arg_idx_vm, arg_value);
    arg_idx_vm += parm_type->size();
  }

  return initial_state;
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_one_bytecode(ciBytecodeStream& parser) {
  MethodState* cur_state = _call_stack.top();
  GrowableArray<Value>& stack = cur_state->stack;
  GrowableArray<Value>& local = cur_state->local;

  auto pop_value = [&]() {
    return this->pop_value(stack);
  };

  auto push_value = [&](Value v) {
    this->push_value(stack, v);
  };

  auto push_type = [&](const Type* t) {
    this->push_type(stack, t);
  };

  assert(parser.cur_bci() < cur_state->method->code_size(), "walked outside the method");
  Bytecodes::Code bc = parser.cur_bc();
  switch (bc) {
    case Bytecodes::_nop:
      break;
    case Bytecodes::_aconst_null:
      push_type(TypePtr::NULL_PTR);
      break;
    case Bytecodes::_iconst_m1:
    case Bytecodes::_iconst_0:
    case Bytecodes::_iconst_1:
    case Bytecodes::_iconst_2:
    case Bytecodes::_iconst_3:
    case Bytecodes::_iconst_4:
    case Bytecodes::_iconst_5:
      push_type(TypeInt::make(bc - Bytecodes::_iconst_0));
      break;
    case Bytecodes::_lconst_0:
    case Bytecodes::_lconst_1:
      push_type(TypeLong::make(bc - Bytecodes::_lconst_0));
      break;
    case Bytecodes::_fconst_0:
    case Bytecodes::_fconst_1:
    case Bytecodes::_fconst_2:
      push_type(TypeF::make(bc - Bytecodes::_fconst_0));
      break;
    case Bytecodes::_dconst_0:
    case Bytecodes::_dconst_1:
      push_type(TypeD::make(bc - Bytecodes::_dconst_0));
      break;
    case Bytecodes::_bipush:
      push_type(TypeInt::make(parser.get_constant_u1()));
      break;
    case Bytecodes::_sipush:
      push_type(TypeInt::make(parser.get_constant_u2()));
      break;
    case Bytecodes::_ldc:
    case Bytecodes::_ldc_w:
    case Bytecodes::_ldc2_w: {
      if (parser.is_in_error()) {
        return Action::CUTOFF;
      }
      ciConstant constant = parser.get_constant();
      if (!constant.is_loaded()) {
        return Action::CUTOFF;
      }
      const Type* con_type = Type::make_from_constant(constant, true);
      assert(con_type != nullptr, "must have a Type");
      push_type(con_type);
      break;
    }
    case Bytecodes::_iload:
    case Bytecodes::_lload:
    case Bytecodes::_fload:
    case Bytecodes::_dload:
    case Bytecodes::_aload:
      push_value(local.at(parser.get_index()));
      break;
    case Bytecodes::_iload_0:
    case Bytecodes::_iload_1:
    case Bytecodes::_iload_2:
    case Bytecodes::_iload_3: {
      Value v = local.at(bc - Bytecodes::_iload_0);
      verify_type(type(v), ciType::make(T_INT));
      push_value(v);
      break;
    }
    case Bytecodes::_lload_0:
    case Bytecodes::_lload_1:
    case Bytecodes::_lload_2:
    case Bytecodes::_lload_3: {
      Value v = local.at(bc - Bytecodes::_lload_0);
      verify_type(type(v), ciType::make(T_LONG));
      push_value(v);
      break;
    }
    case Bytecodes::_fload_0:
    case Bytecodes::_fload_1:
    case Bytecodes::_fload_2:
    case Bytecodes::_fload_3: {
      Value v = local.at(bc - Bytecodes::_fload_0);
      verify_type(type(v), ciType::make(T_FLOAT));
      push_value(v);
      break;
    }
    case Bytecodes::_dload_0:
    case Bytecodes::_dload_1:
    case Bytecodes::_dload_2:
    case Bytecodes::_dload_3: {
      Value v = local.at(bc - Bytecodes::_dload_0);
      verify_type(type(v), ciType::make(T_DOUBLE));
      push_value(v);
      break;
    }
    case Bytecodes::_aload_0:
    case Bytecodes::_aload_1:
    case Bytecodes::_aload_2:
    case Bytecodes::_aload_3: {
      Value v = local.at(bc - Bytecodes::_aload_0);
      verify_type(type(v), ciType::make(T_OBJECT));
      push_value(v);
      break;
    }
    case Bytecodes::_istore:
    case Bytecodes::_lstore:
    case Bytecodes::_fstore:
    case Bytecodes::_dstore:
    case Bytecodes::_astore:
      local.at_put_grow(parser.get_index(), pop_value());
      break;
    case Bytecodes::_istore_0:
    case Bytecodes::_istore_1:
    case Bytecodes::_istore_2:
    case Bytecodes::_istore_3: {
      Value v = pop_value();
      verify_type(type(v), ciType::make(T_INT));
      local.at_put_grow(bc - Bytecodes::_istore_0, v);
      break;
    }
    case Bytecodes::_lstore_0:
    case Bytecodes::_lstore_1:
    case Bytecodes::_lstore_2:
    case Bytecodes::_lstore_3: {
      Value v = pop_value();
      verify_type(type(v), ciType::make(T_LONG));
      local.at_put_grow(bc - Bytecodes::_lstore_0, v);
      break;
    }
    case Bytecodes::_fstore_0:
    case Bytecodes::_fstore_1:
    case Bytecodes::_fstore_2:
    case Bytecodes::_fstore_3: {
      Value v = pop_value();
      verify_type(type(v), ciType::make(T_FLOAT));
      local.at_put_grow(bc - Bytecodes::_fstore_0, v);
      break;
    }
    case Bytecodes::_dstore_0:
    case Bytecodes::_dstore_1:
    case Bytecodes::_dstore_2:
    case Bytecodes::_dstore_3: {
      Value v = pop_value();
      verify_type(type(v), ciType::make(T_DOUBLE));
      local.at_put_grow(bc - Bytecodes::_dstore_0, v);
      break;
    }
    case Bytecodes::_astore_0:
    case Bytecodes::_astore_1:
    case Bytecodes::_astore_2:
    case Bytecodes::_astore_3: {
      Value v = pop_value();
      verify_type(type(v), ciType::make(T_OBJECT));
      local.at_put_grow(bc - Bytecodes::_astore_0, v);
      break;
    }
    case Bytecodes::_pop:
      stack.pop();
      break;
    case Bytecodes::_pop2:
      stack.pop();
      stack.pop();
      break;
    case Bytecodes::_dup:
    case Bytecodes::_dup_x1:
    case Bytecodes::_dup_x2: {
      Value stack_top = stack.top();
      stack.insert_before(stack.length() - 1 - (bc - Bytecodes::_dup), stack_top);
      break;
    }
    case Bytecodes::_dup2:
    case Bytecodes::_dup2_x1:
    case Bytecodes::_dup2_x2: {
      Value elem = stack.at(stack.length() - 2);
      stack.insert_before(stack.length() - 2 - (bc - Bytecodes::_dup2), elem);
      elem = stack.top();
      stack.insert_before(stack.length() - 2 - (bc - Bytecodes::_dup2), elem);
      break;
    }
    case Bytecodes::_swap:
      swap(stack.at(stack.length() - 2), stack.top());
      break;
    case Bytecodes::_iadd:
    case Bytecodes::_isub:
    case Bytecodes::_imul:
    case Bytecodes::_ishl:
    case Bytecodes::_ishr:
    case Bytecodes::_iushr:
    case Bytecodes::_iand:
    case Bytecodes::_ior:
    case Bytecodes::_ixor:
      type(pop_value())->is_int(); type(pop_value())->is_int();
      push_type(TypeInt::INT);
      _num_nodes++;
      break;
    case Bytecodes::_ladd:
    case Bytecodes::_lsub:
    case Bytecodes::_lmul:
    case Bytecodes::_land:
    case Bytecodes::_lor:
    case Bytecodes::_lxor:
      type(pop_value())->is_long(); type(pop_value())->is_long();
      push_type(TypeLong::LONG);
      _num_nodes++;
      break;
    case Bytecodes::_lshl:
    case Bytecodes::_lshr:
    case Bytecodes::_lushr:
      type(pop_value())->is_int(); type(pop_value())->is_long();
      push_type(TypeLong::LONG);
      _num_nodes++;
      break;
    case Bytecodes::_fadd:
    case Bytecodes::_fsub:
    case Bytecodes::_fmul:
    case Bytecodes::_fdiv:
      pop_value(); pop_value();
      push_type(Type::FLOAT);
      _num_nodes++;
      break;
    case Bytecodes::_dadd:
    case Bytecodes::_dsub:
    case Bytecodes::_dmul:
    case Bytecodes::_ddiv:
      pop_value(); pop_value();
      push_type(Type::DOUBLE);
      _num_nodes++;
      break;
    case Bytecodes::_ineg: {
      type(pop_value())->is_int(); push_type(TypeInt::INT);
      _num_nodes++;
      break;
    }
    case Bytecodes::_lneg: {
      type(pop_value())->is_long(); push_type(TypeLong::LONG);
      _num_nodes++;
      break;
    }
    case Bytecodes::_fneg:
      pop_value(); push_type(Type::FLOAT);
      _num_nodes++;
      break;
    case Bytecodes::_dneg:
      pop_value(); push_type(Type::DOUBLE);
      _num_nodes++;
      break;
    case Bytecodes::_iinc: {
      int idx = parser.get_index();
      Value v = local.at(idx);
      verify_type(type(v), ciType::make(T_INT));
      local.at(idx) = make_value(TypeInt::INT);
      _num_nodes++;
      break;
    }
    case Bytecodes::_l2i:
    case Bytecodes::_f2i:
    case Bytecodes::_d2i:
      pop_value(); push_type(TypeInt::INT);
      _num_nodes++;
      break;
    case Bytecodes::_i2l:
    case Bytecodes::_f2l:
    case Bytecodes::_d2l:
      pop_value(); push_type(TypeLong::LONG);
      _num_nodes++;
      break;
    case Bytecodes::_i2f:
    case Bytecodes::_l2f:
    case Bytecodes::_d2f:
      pop_value(); push_type(Type::FLOAT);
      _num_nodes++;
      break;
    case Bytecodes::_i2d:
    case Bytecodes::_l2d:
    case Bytecodes::_f2d:
      pop_value(); push_type(Type::DOUBLE);
      _num_nodes++;
      break;
    case Bytecodes::_i2b:
      type(pop_value())->is_int(); push_type(TypeInt::BYTE);
      _num_nodes++;
      break;
    case Bytecodes::_i2s:
      type(pop_value())->is_int(); push_type(TypeInt::SHORT);
      _num_nodes++;
      break;
    case Bytecodes::_i2c:
      type(pop_value())->is_int(); push_type(TypeInt::CHAR);
      _num_nodes++;
      break;
    case Bytecodes::_lcmp:
    case Bytecodes::_fcmpl:
    case Bytecodes::_fcmpg:
    case Bytecodes::_dcmpl:
    case Bytecodes::_dcmpg:
      pop_value(); pop_value();
      push_type(TypeInt::CC);
      _num_nodes++;
      break;
    case Bytecodes::_ifeq:
      return do_ifeq(parser, pop_value(), make_value(TypeInt::ZERO));
    case Bytecodes::_ifne:
      return do_ifne(parser, pop_value(), make_value(TypeInt::ZERO));
    case Bytecodes::_iflt:
      return do_iflt(parser, pop_value(), make_value(TypeInt::ZERO));
    case Bytecodes::_ifge:
      return do_ifle(parser, make_value(TypeInt::ZERO), pop_value());
    case Bytecodes::_ifgt:
      return do_iflt(parser, make_value(TypeInt::ZERO), pop_value());
    case Bytecodes::_ifle:
      return do_ifle(parser, pop_value(), make_value(TypeInt::ZERO));
    case Bytecodes::_if_icmpeq: {
      Value v2 = pop_value();
      return do_ifeq(parser, pop_value(), v2);
    }
    case Bytecodes::_if_icmpne: {
      Value v2 = pop_value();
      return do_ifne(parser, pop_value(), v2);
    }
    case Bytecodes::_if_icmplt: {
      Value v2 = pop_value();
      return do_iflt(parser, pop_value(), v2);
    }
    case Bytecodes::_if_icmpge: {
      Value v2 = pop_value();
      return do_ifle(parser, v2, pop_value());
    }
    case Bytecodes::_if_icmpgt: {
      Value v2 = pop_value();
      return do_iflt(parser, v2, pop_value());
    }
    case Bytecodes::_if_icmple: {
      Value v2 = pop_value();
      return do_ifle(parser, pop_value(), v2);
    }
    case Bytecodes::_if_acmpeq: {
      Value v2 = pop_value();
      Value v1 = pop_value();
      if (v1.id() == v2.id()) {
        parser.reset_to_bci(parser.get_dest());
        return Action::CONTINUE;
      }

      const TypePtr* t1 = type(v1)->is_ptr();
      const TypePtr* t2 = type(v2)->is_ptr();
      if (t1->singleton() && t2->singleton() && t1 == t2) {
        parser.reset_to_bci(parser.get_dest());
        return Action::CONTINUE;
      } else if (t1->isa_oopptr() && t2->isa_oopptr() && t1->join(t2)->empty()) {
        return Action::CONTINUE;
      } else {
        return Action::NOT_TRIVIAL;
      }
    }
    case Bytecodes::_if_acmpne: {
      Value v2 = pop_value();
      Value v1 = pop_value();
      if (v1.id() == v2.id()) {
        return Action::CONTINUE;
      }

      const TypePtr* t1 = type(v1)->is_ptr();
      const TypePtr* t2 = type(v2)->is_ptr();
      if (t1->singleton() && t2->singleton() && t1 == t2) {
        return Action::CONTINUE;
      } else if (t1->isa_oopptr() && t2->isa_oopptr() && t1->join(t2)->empty()) {
        parser.reset_to_bci(parser.get_dest());
        return Action::CONTINUE;
      } else {
        return Action::NOT_TRIVIAL;
      }
    }
    case Bytecodes::_goto:
      parser.reset_to_bci(parser.get_dest());
      return Action::CONTINUE;
    case Bytecodes::_goto_w:
      parser.reset_to_bci(parser.get_far_dest());
      return Action::CONTINUE;
    case Bytecodes::_ireturn:
    case Bytecodes::_lreturn:
    case Bytecodes::_freturn:
    case Bytecodes::_dreturn:
    case Bytecodes::_areturn: {
      Value ret_value = pop_value();
      _call_stack.pop();
      if (_call_stack.is_nonempty()) {
        MethodState* caller_state = _call_stack.top();
        this->push_value(caller_state->stack, ret_value);
      }
      return Action::RETURN;
    }
    case Bytecodes::_return:
      _call_stack.pop();
      return Action::RETURN;
    case Bytecodes::_getstatic:
    case Bytecodes::_putstatic:
      return do_static_field(parser);
    case Bytecodes::_getfield:
    case Bytecodes::_putfield:
      return do_instance_field(parser);
    case Bytecodes::_invokevirtual:
    case Bytecodes::_invokespecial:
    case Bytecodes::_invokestatic:
    case Bytecodes::_invokeinterface:
      return do_call(parser);
    case Bytecodes::_arraylength:
      return do_array_length(parser);
    case Bytecodes::_ifnull: {
      const Type* t = type(pop_value());
      if (t == TypePtr::NULL_PTR) {
        parser.reset_to_bci(parser.get_dest());
        return Action::CONTINUE;
      } else if (t->join(TypePtr::NULL_PTR)->empty()) {
        return Action::CONTINUE;
      } else {
        return Action::NOT_TRIVIAL;
      }
    }
    case Bytecodes::_ifnonnull: {
      const Type* t = type(pop_value());
      if (t == TypePtr::NULL_PTR) {
        return Action::CONTINUE;
      } else if (t->join(TypePtr::NULL_PTR)->empty()) {
        parser.reset_to_bci(parser.get_dest());
        return Action::CONTINUE;
      } else {
        return Action::NOT_TRIVIAL;
      }
    }
    default:
      return Action::NOT_TRIVIAL;
  }

  return Action::CONTINUE;
}

BCTrivialAnalyzer::Value BCTrivialAnalyzer::make_value(const Type* t) {
  Value v = _provider.get();
  set_type(v, t);
  return v;
}

const Type* BCTrivialAnalyzer::type(Value v) {
  const Type* res = _types.at(v.id());
  assert(res != nullptr, "must set_type before");
  return res;
}

void BCTrivialAnalyzer::set_type(Value v, const Type* t) {
  assert(t != nullptr, "must not pass nullptr");
  _types.at_put_grow(v.id(), t);
}

BCTrivialAnalyzer::Value BCTrivialAnalyzer::pop_value(GrowableArray<Value>& stack) {
  Value res = stack.pop();
  if (!res.is_valid()) {
    res = stack.pop();
    assert(res.is_valid(), "cannot have 2 consecutive placeholders");
    const Type* t = type(res);
    assert(t->isa_long() || t->isa_double(),
           "must be a 2-slot type %s %d", type2name(t->basic_type()), t->base());
  }
  return res;
}

void BCTrivialAnalyzer::push_value(GrowableArray<Value>& stack, Value v) {
  assert(v.is_valid(), "must not push an invalid Value");
  stack.push(v);
  const Type* t = type(v);
  if (t->isa_long() || t->isa_double()) {
    // Use an invalid Value as the placeholder
    stack.push(Value());
  }
}

void BCTrivialAnalyzer::push_type(GrowableArray<Value>& stack, const Type* t) {
  assert(t != nullptr, "must not pass nullptr");
  push_value(stack, make_value(t));
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_ifeq(ciBytecodeStream& parser, Value v1, Value v2) {
  if (v1.id() == v2.id()) {
    parser.reset_to_bci(parser.get_dest());
    return Action::CONTINUE;
  }

  const TypeInt* t1 = type(v1)->is_int();
  const TypeInt* t2 = type(v2)->is_int();
  if (t1->is_con() && t2->is_con() && t1->get_con() == t2->get_con()) {
    parser.reset_to_bci(parser.get_dest());
    return Action::CONTINUE;
  } else if (t1->join(t2)->empty()) {
    return Action::CONTINUE;
  } else {
    return Action::NOT_TRIVIAL;
  }
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_ifne(ciBytecodeStream& parser, Value v1, Value v2) {
  if (v1.id() == v2.id()) {
    return Action::CONTINUE;
  }

  const TypeInt* t1 = type(v1)->is_int();
  const TypeInt* t2 = type(v2)->is_int();
  if (t1->join(t2)->empty()) {
    parser.reset_to_bci(parser.get_dest());
    return Action::CONTINUE;
  } else if (t1->is_con() && t2->is_con() && t1->get_con() == t2->get_con()) {
    return Action::CONTINUE;
  } else {
    return Action::NOT_TRIVIAL;
  }
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_iflt(ciBytecodeStream& parser, Value v1, Value v2) {
  if (v1.id() == v2.id()) {
    return Action::CONTINUE;
  }

  const TypeInt* t1 = type(v1)->is_int();
  const TypeInt* t2 = type(v2)->is_int();
  if (t1->_hi < t2->_lo) {
    parser.reset_to_bci(parser.get_dest());
    return Action::CONTINUE;
  } else if (t1->_lo >= t2->_hi) {
    return Action::CONTINUE;
  } else {
    return Action::NOT_TRIVIAL;
  }
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_ifle(ciBytecodeStream& parser, Value v1, Value v2) {
  if (v1.id() == v2.id()) {
    parser.reset_to_bci(parser.get_dest());
    return Action::CONTINUE;
  }

  const TypeInt* t1 = type(v1)->is_int();
  const TypeInt* t2 = type(v2)->is_int();
  if (t1->_hi <= t2->_lo) {
    parser.reset_to_bci(parser.get_dest());
    return Action::CONTINUE;
  } else if (t1->_lo > t2->_hi) {
    return Action::CONTINUE;
  } else {
    return Action::NOT_TRIVIAL;
  }
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_static_field(ciBytecodeStream& parser) {
  bool will_link;
  ciField* field = parser.get_field(will_link);
  if (!will_link) {
    return Action::CUTOFF;
  }

  assert(field->is_static(), "must be a static field %s.%s", field->holder()->name()->as_utf8(), field->name()->as_utf8());
  if (!field->holder()->is_initialized()) {
    // We may need a clinit barrier here
    return Action::NOT_TRIVIAL;
  }

  GrowableArray<Value>& stack = _call_stack.top()->stack;
  Bytecodes::Code bc = parser.cur_bc();

  // Try to constant fold the load
  if (bc == Bytecodes::_getstatic && field->is_constant()) {
    ciConstant field_value = field->constant_value();
    if (field_value.is_valid()) {
      push_type(stack, Type::make_from_constant(field_value, true));
      return Action::CONTINUE;
    }
  }

  if (bc == Bytecodes::_getstatic) {
    push_type(stack, Type::get_const_type(field->type()));
  } else {
    Value val = pop_value(stack);
    verify_type(type(val), field->type());
  }

  // This will result in an AddPNode and a MemNode
  _num_nodes += 2;
  return Action::CONTINUE;
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_instance_field(ciBytecodeStream& parser) {
  bool will_link;
  ciField* field = parser.get_field(will_link);
  if (!will_link) {
    return Action::CUTOFF;
  }

  MethodState* cur_state = _call_stack.top();
  GrowableArray<Value>& stack = cur_state->stack;
  Bytecodes::Code bc = parser.cur_bc();
  assert(!field->is_static(), "must be an instance field %s.%s", field->holder()->name()->as_utf8(), field->name()->as_utf8());
  if (bc == Bytecodes::_putfield) {
    Value val = pop_value(stack);
    verify_type(type(val), field->type());
  }

  Value obj_value = pop_value(stack);
  const TypePtr* obj_type = type(obj_value)->is_ptr();
  if (obj_type->maybe_null() && C->too_many_traps(cur_state->method, parser.cur_bci(), Deoptimization::Reason_null_check)) {
    // May generate a throw instead of a trap for the null check
    return Action::NOT_TRIVIAL;
  } else if (obj_type == TypePtr::NULL_PTR) {
    return Action::CUTOFF;
  }

  // Try to constant fold the load
  assert(obj_type->isa_instptr(), "must be a non-array object");
  ciObject* obj_con = obj_type->is_instptr()->const_oop();
  if (bc == Bytecodes::_getfield && obj_con != nullptr && field->is_constant()) {
    ciConstant field_value = field->constant_value_of(obj_con);
    if (field_value.is_valid()) {
      push_type(stack, Type::make_from_constant(field_value, true));
      return Action::CONTINUE;
    }
  }

  if (obj_type->maybe_null()) {
    // Indicate that the object is not null from here
    obj_type = obj_type->join(TypePtr::NOTNULL)->is_ptr();
    set_type(obj_value, obj_type);

    // The null check will result in 4 nodes ignoring the trap path, which are a CmpP, a Bool, an
    // If and an IfProj
    _num_nodes += 4;
  }

  if (bc == Bytecodes::_getfield) {
    push_type(stack, Type::get_const_type(field->type()));
  }

  // This will result in an AddPNode and a MemNode, intentionally ignore the null check as it
  // usually results in no code
  _num_nodes += 2;
  return Action::CONTINUE;
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_call(ciBytecodeStream& parser) {
  // Inlining a method will not simplify the graph if it results in another call. As a result, the
  // root method is only trivial if we can inline this callee and the result is still trivial.
  if (_call_stack.length() >= MaxForceInlineLevel) {
    return Action::NOT_TRIVIAL;
  }

  bool will_link;
  ciSignature* declared_signature = nullptr;
  ciMethod* callee = parser.get_method(will_link, &declared_signature);
  if (!will_link) {
    // Field accesses will generate a trap when it can't be linked at compile-time, it is not true
    // for method invocations
    return Action::NOT_TRIVIAL;
  }

  bool polymorphic_signature = MethodHandles::is_signature_polymorphic(callee->intrinsic_id());
  if (polymorphic_signature || parser.has_appendix() || Bytecodes::has_optional_appendix(parser.cur_bc_raw())) {
    // Method-handle-related, can push additional arguments on the stack and change the return type
    // arbitrarily. Not supported
    return Action::NOT_TRIVIAL;
  }

  MethodState* cur_state = _call_stack.top();
  ciMethod* cur_method = cur_state->method;
  GrowableArray<Value>& stack = cur_state->stack;
  Bytecodes::Code bc = parser.cur_bc();
  bool has_receiver = (bc != Bytecodes::_invokestatic);
  assert(has_receiver != callee->is_static(), "mismatched bytecode %s for callee %s::%s",
         Bytecodes::name(bc), callee->holder()->name()->as_utf8(), callee->name()->as_utf8());

  if (has_receiver) {
    Value receiver = stack.at(stack.length() - callee->arg_size());
    const TypePtr* receiver_type = type(receiver)->is_ptr();
    if (receiver_type->maybe_null() && C->too_many_traps(cur_method, parser.cur_bci(), Deoptimization::Reason_null_check)) {
      // May generate a throw instead of a trap for the null check
      return Action::NOT_TRIVIAL;
    } else if (receiver_type == TypePtr::NULL_PTR) {
      return Action::CUTOFF;
    }

    bool dynamic_dispatch = (bc == Bytecodes::_invokevirtual || bc == Bytecodes::_invokeinterface);
    if (dynamic_dispatch) {
      ciKlass* declared_holder = parser.get_declared_method_holder();
      ciInstanceKlass* declared_instance_holder = ciEnv::get_instance_klass_for_declared_method_holder(declared_holder);
      int vtable_index = Method::invalid_vtable_index;
      callee = C->optimize_virtual_call(cur_method, declared_instance_holder, declared_holder, callee,
                                        receiver_type->is_oopptr(), bc == Bytecodes::_invokevirtual,
                                        dynamic_dispatch, vtable_index);

      if (dynamic_dispatch) {
        // Cannot inline a virtual call that requires dynamic dispatch
        return Action::NOT_TRIVIAL;
      }
    }

    if (receiver_type->maybe_null()) {
      // Indicate that receiver is not null from here
      receiver_type = receiver_type->join(TypePtr::NOTNULL)->is_ptr();
      set_type(receiver, receiver_type);

      // The null check will result in 4 nodes ignoring the trap path, which are a CmpP, a Bool, an
      // If and an IfProj
      _num_nodes += 4;
    }

    // Improve the receiver type based on the found callee 
    const TypeOopPtr* callee_receiver_type = TypeOopPtr::make_from_klass(callee->holder());
    if (!receiver_type->higher_equal(callee_receiver_type)) {
      // A type check is necessary before invoking the callee, which can be considered not trivial
      return Action::NOT_TRIVIAL;
    }
  }

  if (InlineTree::check_can_parse(callee) != nullptr) {
    return Action::NOT_TRIVIAL;
  }

  // Check for recursion
  for (int i = 0; i < _call_stack.length(); i++) {
    if (_call_stack.at(i)->method == callee) {
      return Action::NOT_TRIVIAL;
    }
  }

  // Create a state for the callee on call_stack
  MethodState* callee_state = new MethodState(callee);
  if (has_receiver) {
    Value receiver = stack.at(stack.length() - callee->arg_size());
    callee_state->local.at_put_grow(0, receiver);
  }

  int arg_start = has_receiver ? 1 : 0;
  for (int i = 0, j = arg_start; j < callee->arg_size(); i++) {
    Value arg = stack.at(stack.length() - callee->arg_size() + j);
    ciType* parm_type = callee->signature()->type_at(i);
    verify_type(type(arg), parm_type);
    callee_state->local.at_put_grow(j, arg);
    j += parm_type->size();
  }
  _call_stack.push(callee_state);

  // Modify the current state, the callee will push the return value upon returning there
  stack.trunc_to(stack.length() - callee->arg_size());
  cur_state->bci = parser.next_bci();
  return Action::CALL;
}

BCTrivialAnalyzer::Action BCTrivialAnalyzer::do_array_length(ciBytecodeStream& parser) {
  MethodState* cur_state = _call_stack.top();
  ciMethod* cur_method = cur_state->method;
  GrowableArray<Value>& stack = cur_state->stack;

  Value array = pop_value(stack);
  const TypePtr* array_type = type(array)->is_ptr();
  if (array_type->maybe_null() && C->too_many_traps(cur_method, parser.cur_bci(), Deoptimization::Reason_null_check)) {
    // May generate a throw instead of a trap for the null check
    return Action::NOT_TRIVIAL;
  } else if (array_type == TypePtr::NULL_PTR) {
    return Action::CUTOFF;
  }

  if (array_type->maybe_null()) {
    // Indicate that the array is not null from here
    array_type = array_type->is_aryptr()->join(TypePtr::NOTNULL)->is_ptr();
    set_type(array, array_type);

    // The null check will result in 4 nodes ignoring the trap path, which are a CmpP, a Bool, an
    // If and an IfProj
    _num_nodes += 4;
  }

  const TypeInt* length_type = array_type->is_aryptr()->size();
  push_type(stack, length_type);
  if (!length_type->is_con()) {
    // This will result in an AddPNode and a LoadRangeNode
    _num_nodes += 2;
  }
  return Action::CONTINUE;
}

void BCTrivialAnalyzer::verify_type(const Type* arg, ciType* parm_type) {
  BasicType arg_bt = arg->basic_type();
  BasicType parm_bt = parm_type->basic_type();
  assert(arg_bt == parm_bt || (arg_bt == T_INT && is_subword_type(parm_bt)) ||
         ((arg_bt == T_OBJECT || arg_bt == T_ADDRESS) && (parm_bt == T_OBJECT || parm_bt == T_ARRAY)),
         "Mismatch parameter %s - argument %s", type2name(parm_bt), type2name(arg_bt));
}

void* BCTrivialAnalyzer::MethodState::operator new(size_t size) {
  return ArenaObj::operator new(size, Thread::current()->resource_area());
}
