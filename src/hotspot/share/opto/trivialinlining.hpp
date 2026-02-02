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

#ifndef SHARE_OPTO_TRIVIALINLINING_HPP
#define SHARE_OPTO_TRIVIALINLINING_HPP

#include "libadt/vectset.hpp"
#include "memory/allocation.hpp"
#include "utilities/growableArray.hpp"

class ciBytecodeStream;
class ciMethod;
class ciType;
class Compile;
class GraphKit;
class JVMState;
class Type;
class TypeInt;

// If inlining a method makes the graph simpler than not inlining it, then it is always profitable
// to inline that method regardless of other heuristics. Implementation-wise, for the inlining
// purposes, a trivial method does not introduce any control flow except traps, and even in the
// worst case, it generates a small amount of nodes.
//
// This class implements a fast bytecode analysis to determine whether a method is trivial for the
// purpose of inlining at a certain context. Since it is not always easy to determine if inlining a
// method would simplify the graph, this class should be conservative.
//
// This class does the analysis by doing a simplified simulation of the execution of the inspected
// method. It continues until either it concludes that the inspected callee is not trivial when
// called from the current context, or the simulation ends because the inspected method has
// returned, or the simulation ends because it reaches a trap such as loading from/storing into a
// field of an object that turns out to be a null constant. If the simulation ends without the
// analyzer concluding that the inspected method is non-trivial, then it is considered trivial, and
// the compiler will try harder to inline it.
class BCTrivialAnalyzer : StackObj {
public:
  static bool is_trivial(ciMethod* callee, JVMState* caller_state);

private:
  class ValueProvider;

  // The identity of a value, similar to a node in the graph
  class Value {
  private:
    int _v;

    explicit Value(int v) : _v(v) {}

    friend class ValueProvider;

  public:
    Value() : _v(-1) {}

    int id() const { assert(is_valid(), "invalid"); return _v; }
    bool is_valid() const { return _v >= 0; }
  };

  // Use to ensure all the values have distinct non-negative identity values
  class ValueProvider {
  private:
    int _current_idx;

  public:
    ValueProvider() : _current_idx(0) {}

    Value get() { return Value(_current_idx++); }
  };

  class MethodState : public ArenaObj {
  public:
    ciMethod* const method;
    GrowableArray<Value> stack;
    GrowableArray<Value> local;
    VectorSet visited_bci;
    int bci;

    MethodState(ciMethod* method) : method(method), stack(), local(), visited_bci(), bci(0) {}

    void* operator new(size_t size);
  };

  Compile* C;

  // Inlining a method will not simplify the graph if it results in another call, we need to try
  // inlining the callee, too. This _call_stack helps save the state of a method at an invoke
  // instruction, and restores them when the callee of that invoke instruction returns.
  GrowableArray<MethodState*> _call_stack;

  // Number of nodes created if the inspected method is inlined, ignore constants
  int _num_nodes;

  ValueProvider _provider;

  // Map each value to its Type
  GrowableArray<const Type*> _types;

  BCTrivialAnalyzer(Compile* C) : C(C), _call_stack(), _num_nodes(0) {}

  // The action the analyzer should take after processing one bytecode
  enum class Action {
    // Continue with processing the current method, the parser can just call next() to process the
    // next bytecode. It has either fallen through to the next bytecode, or followed an
    // unconditional jump. If the parser has followed an unconditional jump, we need to call
    // reset_to_bci to tell the parser that the next bytecode to process is the destination of the
    // jump.
    CONTINUE,

    // The current method has returned, it has pushed the result on the stack of the caller and
    // popped the MethodState corresponding to itself from _call_stack. We need to stop the
    // execution and continue processing the caller, which is the top entry on _call_stack now.
    RETURN,

    // The current method has called another method, it has pushed the initial state of the callee
    // as a MethodState on _call_stack. We need to pause the execution of the current method and
    // start processing the callee, which is the top entry on _call_stack now.
    CALL,

    // The analyzer concludes that the inspected method (the root method on _call_stack) is not
    // trivial in the current context. It can be because either the analyzer encounters a
    // conditional jump that cannot be folded, or there have been too many nodes created for the
    // root method to be considered trivial, or any unexpected circumstance that we decide to be
    // conservative such as unhandled bytecodes.
    NOT_TRIVIAL,

    // The analyzer concludes that the path would be cut off due to reaching a trap (e.g. loading
    // a field from a null constant). The simulation ends immediately, the root method is
    // considered trivial, and it is extra beneficial because the compiler will know that this path
    // is a dead end.
    CUTOFF
  };

  MethodState* prepare_initial_state(ciMethod* callee, JVMState* caller_state);
  Action do_one_bytecode(ciBytecodeStream& parser);

  // General helper methods
  Value make_value(const Type* t);
  const Type* type(Value v);
  void set_type(Value v, const Type* t);
  Value pop_value(GrowableArray<Value>& stack);
  void push_value(GrowableArray<Value>& stack, Value v);
  void push_type(GrowableArray<Value>& stack, const Type* t);

  // Helper methods for branching bytecodes
  Action do_ifeq(ciBytecodeStream& parser, Value v1, Value v2);
  Action do_ifne(ciBytecodeStream& parser, Value v1, Value v2);
  Action do_iflt(ciBytecodeStream& parser, Value v1, Value v2);
  Action do_ifle(ciBytecodeStream& parser, Value v1, Value v2);

  Action do_static_field(ciBytecodeStream& parser);
  Action do_instance_field(ciBytecodeStream& parser);
  Action do_call(ciBytecodeStream& parser);
  Action do_array_length(ciBytecodeStream& parser);

  static void verify_type(const Type* arg_type, ciType* parm_type);
};

#endif // SHARE_OPTO_TRIVIALINLINING_HPP
