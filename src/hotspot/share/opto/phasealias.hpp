/*
 * Copyright (c) 2025, Oracle and/or its affiliates. All rights reserved.
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

#ifndef SHARE_OPTO_PHASEALIAS_HPP
#define SHARE_OPTO_PHASEALIAS_HPP

#include "libadt/vectset.hpp"
#include "opto/phase.hpp"
#include "utilities/growableArray.hpp"

class ciKlass;
class MemNode;
class MergeMemNode;
class NarrowMemProjNode;
class PhaseIterGVN;
class PhiNode;
class TypeAryPtr;
class TypeOopPtr;
class TypePtr;
class Unique_Node_List;

class AliasAnalyzer {
public:
  AliasAnalyzer() : _analyzed(false) {}

  const TypeOopPtr* flatten_alias_type(Compile* C, const TypeOopPtr* ptr) const;

private:
  friend class PhaseAliasAnalysis;

  bool _analyzed;

  class MemorySlice {
  public:
    const TypeOopPtr* _base;
    int _offset;
    int _size;

    MemorySlice() : _base(nullptr), _offset(-1), _size(-1) {}
    MemorySlice(const TypeOopPtr* base, int offset, int size);
    static bool not_overlap(const MemorySlice& x, const MemorySlice& y);
    static MemorySlice combine(const MemorySlice& x, const MemorySlice& y);

    bool operator==(const MemorySlice& o) const;
  };
};

class PhaseAliasAnalysis : public Phase {
public:
  PhaseAliasAnalysis(AliasAnalyzer& analyzer, PhaseIterGVN& igvn);
  void optimize();

private:
  AliasAnalyzer& _analyzer;
  PhaseIterGVN& _igvn;

  // The index of the alias class corresponding to all heap memory before this phase
  const int _old_oop_alias_idx;

  // The number of alias classes before this phase
  const int _old_alias_limit;

  // The result of splitting heap accesses into non-overlapping memory slices, an alias class is
  // made corresponding to each of these slices
  GrowableArray<AliasAnalyzer::MemorySlice>* _memory_slices;

  // All nodes in the graph before PhaseAliasAnalysis
  Unique_Node_List* _old_nodes;

  // If a MergeMem has memory at _old_oop_alias_idx different from the base memory, we need to find
  // the correct memory for each of the newly created alias classes and connect them to the
  // MergeMem during this phase
  Unique_Node_List* _merge_mems;

  // Before alias analysis, a Phi and NarrowMemProj represents the state of the whole heap, we need
  // to split them so that 1 Phi or NarrowMemProj represents only 1 alias class
  Unique_Node_List* _old_phis_narrow_projs;

  void analyze();
  void do_transform();

  // A data structure to contain the information needed to perform splitting the memory graph
  class SplitMemoryGraphData {
  public:
    // At each memory node, we can record the correct memory for each of the split slice.
    // For example, given this simple graph:
    // Start -> Store A.a -> Store A.b -> Store B.v
    // Then, at the node Store B.v, the memory state of the alias class B.v would be that node
    // itself, while the memory state of the alias class A.a would be the node Store A.a, and the
    // memory state of an unrelated alias class (e.g int[]) would be Start.
    // As a result, if we denote the memory state as (Bottom, A.a, A.b, B.v, int[]), then:
    // the memory state at Store A.a will be (Start, Store A.a, Start, Start, Start)
    // the memory state at Store A.b will be (Start, Store A.a, Store A.b, Start, Start)
    // the memory state at Store B.v will be (Start, Store A.a, Store A.b, Store B.v, Start)
    // However, it would be expensive to record the states of all alias classes at each memory
    // node. So, we only record the states at Phis and NarrowMemProjs here. This is because before
    // alias analysis, each Phi/NarrowMemProj represents the whole state of heap memory and we need
    // to split them into 1 for each newly created alias class.
    GrowableArray<Node**> split_mem_nodes;

    // Besides Phis and MergeMems, each node can only consume not more than 1 memory input. If the
    // memory input of a node needs changing, record it here.
    GrowableArray<Node*> memory_inputs;

    // Data structures shared between iterations
    GrowableArray<Node*> alias_states;
    GrowableArray<Node*> work_stack;
    VectorSet visited;

    SplitMemoryGraphData(PhaseAliasAnalysis& alias_analysis);
  };

  static void add_slice(GrowableArray<AliasAnalyzer::MemorySlice>& current_slices, AliasAnalyzer::MemorySlice new_slice);
  static void verify_slices(const GrowableArray<AliasAnalyzer::MemorySlice>& memory_slices);
  bool check_node_limit();
  void create_alias_classes();
  void split_memory_graph();
  void split_memory_nodes(SplitMemoryGraphData& data);
  void record_memory_edges(SplitMemoryGraphData& data);
  void fix_memory_edges(const SplitMemoryGraphData& data);

  template <class F>
  void record_memory_edges_from_states(F fix_states, SplitMemoryGraphData& data, Node* start_input);

  int alias_index(const AliasAnalyzer::MemorySlice& alias_slice);
  static uint memory_input_idx(Node* n);
  static const TypePtr* get_adr_type(Node* n);

  static AliasAnalyzer::MemorySlice heap_access_slice(const TypeOopPtr* ptr, int memory_size);
  static void normalize_aryptr(const TypeAryPtr*& ptr, int& offset);

  template <class F>
  void for_each_narrow_mem_proj_slice(F f, NarrowMemProjNode* node);

  ciKlass* narrow_mem_alloc_klass(NarrowMemProjNode* node, bool& is_exact);

  void verify_graph();
  Node* find_new_memory_input(const SplitMemoryGraphData& data, Node* in, int alias_idx);
};

#endif // SHARE_OPTO_PHASEALIAS_HPP
