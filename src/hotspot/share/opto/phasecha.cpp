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
#include "ci/ciKlass.hpp"
#include "memory/resourceArea.hpp"
#include "opto/c2_globals.hpp"
#include "opto/callnode.hpp"
#include "opto/castnode.hpp"
#include "opto/node.hpp"
#include "opto/phasecha.hpp"
#include "opto/rootnode.hpp"
#include "opto/type.hpp"
#include "utilities/growableArray.hpp"
#include "utilities/macros.hpp"

void PhaseCHA::do_transform() {
  if (C->dependencies() == nullptr) {
    return;
  }

  ResourceMark rm;
  Unique_Node_List worklist;
  RootNode* root = C->root();
  worklist.push(root);

  for (uint wl_idx = 0; wl_idx < worklist.size(); wl_idx++) {
    Node* n = worklist.at(wl_idx);
    optimize_node_type(n);

    for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
      worklist.push(n->fast_out(i));
    }
  }
  DEBUG_ONLY(verify(worklist));
}

// Given an oop, try to infer a better type for that pointer using class hierarchy analysis.
// - If it is an oop to an abstract class, and that abstract class has a single concrete subklass,
//   then the oop must point to an instance of that concrete subklass.
// - If the oop implements an interface, and that interface has a unique implementor, then the oop
//   must point to an instance of that unique implementor.
void PhaseCHA::optimize_node_type(Node* n) {
  bool should_process = n->is_Start() || n->is_Call() || n->is_Type() || n->is_Load();
  if (!should_process) {
    return;
  }

  if (n->is_Start()) {
    StartNode* start = n->as_Start();
    const TypeTuple* new_type = optimize_tuple_type(start->_domain);
    if (new_type != nullptr) {
      _igvn.rehash_node_delayed(start);
      start->_domain = new_type;
    }
  } else if (n->is_Call()) {
    CallNode* call = n->as_Call();
    const TypeFunc* call_type = call->tf();
    const TypeTuple* new_range_sig = optimize_tuple_type(call_type->range_sig());
    const TypeTuple* new_range_cc = optimize_tuple_type(call_type->range_cc());
    if (new_range_sig != nullptr || new_range_cc != nullptr) {
      if (new_range_sig == nullptr) {
        new_range_sig = call_type->range_sig();
      }
      if (new_range_cc == nullptr) {
        new_range_cc = call_type->range_cc();
      }

      auto new_call_type = TypeFunc::make(call_type->domain_sig(), call_type->domain_cc(),
                                          new_range_sig, new_range_cc, call_type->returns_value_type_as_fields());
      _igvn.rehash_node_delayed(call);
      call->set_tf(new_call_type);
    }
  } else {
    const Type* new_type = optimize_inst_oop_type(n->bottom_type()->isa_instptr());
    if (new_type != nullptr) {
      _igvn.rehash_node_delayed(n);
      n->raise_bottom_type(new_type);
    }
  }
}

// Try to optimize a TypeInstPtr to a narrower type with CHA
const Type* PhaseCHA::optimize_inst_oop_type(const TypeInstPtr* type) {
  if (type == nullptr || type->klass_is_exact() || type->offset() != 0) {
    return nullptr;
  }

  ciInstanceKlass* improved_klass = optimize_instance_klass(type->instance_klass(), type->interfaces());
  if (improved_klass == nullptr) {
    return nullptr;
  }

  const Type* new_type = TypeOopPtr::make_from_klass(improved_klass)->filter(type);
  assert(!new_type->empty(), "cannot degenerate to TOP");
  return new_type;
}

// Try to optimize a TypeTuple if any of its fields can be optimized to a narrower type with CHA
const TypeTuple* PhaseCHA::optimize_tuple_type(const TypeTuple* type) {
  const Type** new_elems = nullptr;
  for (uint elem_idx = 0; elem_idx < type->cnt(); elem_idx++) {
    const Type* elem = type->field_at(elem_idx);
    const Type* new_elem = optimize_inst_oop_type(elem->isa_instptr());
    if (new_elem == nullptr) {
      if (new_elems != nullptr) {
        new_elems[elem_idx] = elem;
      }
    } else {
      if (new_elems == nullptr) {
        new_elems = TypeTuple::fields(type->cnt() - TypeFunc::Parms);
        for (uint i = 0; i < elem_idx; i++) {
          new_elems[i] = type->field_at(i);
        }
      }

      new_elems[elem_idx] = new_elem;
    }
  }

  if (new_elems == nullptr) {
    return nullptr;
  }

  return TypeTuple::make(type->cnt(), new_elems);
}

ciInstanceKlass* PhaseCHA::optimize_instance_klass(ciInstanceKlass* klass, const TypeInterfaces* interfaces) {
  if (!UseUniqueSubclasses || !klass->is_loaded()) {
    return nullptr;
  }

  ciInstanceKlass* improved_klass = klass;
  if (ciInstanceKlass* unique_subklass = klass->unique_concrete_subklass_checked(); unique_subklass != nullptr) {
    C->dependencies()->assert_abstract_with_unique_concrete_subtype(klass, unique_subklass);
    improved_klass = unique_subklass;
  }

  {
    ResourceMark rm;
    GrowableArray<ciInstanceKlass*> interface_list;
    interfaces->collect(interface_list);
    for (ciInstanceKlass* interface : interface_list) {
      ciInstanceKlass* unique_implementor = interface->unique_implementor_checked();
      // We may take advantage of the case that klass and implementor are unrelated and update n to
      // top. However, it is more of a safeguard mechanism to ensure that this phase does not miss
      // working with conditions, because the path should be killed.
      if (unique_implementor != nullptr && unique_implementor != improved_klass && unique_implementor->is_subclass_of(improved_klass)) {
        C->dependencies()->assert_unique_implementor(interface, unique_implementor);
        improved_klass = unique_implementor;
      }
    }
  }

  assert(improved_klass->is_subclass_of(klass), "must always obtain a narrower or equal type");
  return improved_klass == klass ? nullptr : improved_klass;
}

ciKlass* PhaseCHA::klassptr_type_has_no_subklass(const TypeKlassPtr* type) {
  const TypeInstKlassPtr* inst_type = type->isa_instklassptr();
  if (inst_type == nullptr) {
    return nullptr;
  }

  ciInstanceKlass* inst_klass = inst_type->instance_klass();
  if (!inst_klass->has_subklass_checked() && inst_type->interfaces()->eq(inst_klass)) {
    C->dependencies()->assert_leaf_type(inst_klass);
    return inst_klass;
  }

  return nullptr;
}

#ifdef ASSERT
void PhaseCHA::verify(const Unique_Node_List& node_list) {
  for (uint nl_idx = 0; nl_idx < node_list.size(); nl_idx++) {
    Node* n = node_list.at(nl_idx);
    if (n->is_CastPP()) {
      CastPPNode::verify_type(n->in(1)->bottom_type(), n->bottom_type());
    } else if (n->is_Phi() && n->bottom_type()->isa_ptr() != nullptr) {
      const Type* phi_type = n->bottom_type();
      for (uint i = 1; i < n->req(); i++) {
        assert(n->in(i)->bottom_type()->higher_equal(phi_type), "a Phi's Type must be wider than the Types of its inputs");
      }
    }
  }
}
#endif // ASSERT
