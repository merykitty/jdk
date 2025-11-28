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

#include "opto/phasealias.hpp"
#include "ci/ciInstanceKlass.hpp"
#include "ci/ciObject.hpp"
#include "memory/allocation.hpp"
#include "memory/resourceArea.hpp"
#include "opto/arraycopynode.hpp"
#include "opto/callnode.hpp"
#include "opto/compile.hpp"
#include "opto/memnode.hpp"
#include "opto/multnode.hpp"
#include "opto/node.hpp"
#include "opto/opcodes.hpp"
#include "opto/phase.hpp"
#include "opto/phaseX.hpp"
#include "opto/rootnode.hpp"
#include "opto/type.hpp"
#include "utilities/debug.hpp"
#include "utilities/growableArray.hpp"
#include "utilities/ostream.hpp"

#include <cstring>

constexpr bool VerifyAliasAnalysis = true;

// Do not try to add a slice which seems too large, it is better to drop them to TypeOopPtr::BOTTOM
// instead. This will make that particular access less optimized but avoid degrade other accesses
// that may alias if this absorbs them.
static bool should_not_try_analyze(const TypePtr* ptr) {
  if (!ptr->isa_instptr()) {
    return false;
  }
  if (ptr->offset() == Type::OffsetBot) {
    return true;
  }
  ciInstanceKlass* klass = ptr->is_instptr()->instance_klass();
  // j.l.Class contains hidden fields and static fields
  if (klass == ciEnv::current()->Class_klass()) {
    return false;
  }
  return klass->get_field_by_offset(ptr->offset(), false) == nullptr;
}

const TypeOopPtr* AliasAnalyzer::flatten_alias_type(Compile* C, const TypeOopPtr* ptr) const {
  assert(!ptr->is_known_instance(), "known instances do not need flattening");
  if (should_not_try_analyze(ptr)) {
    // Return a dubious alias class, cannot return TypePtr::BOTTOM, although it is arguably more
    // correct, because there are places expecting only TypePtr::BOTTOM to return AliasIdxBot
    return TypeOopPtr::BOTTOM;
  }

  if (!_analyzed || ptr == TypeOopPtr::BOTTOM) {
    return TypeOopPtr::BOTTOM;
  }

  MemorySlice ptr_slice = MemorySlice(ptr->with_offset(0), ptr->offset(), ptr->offset() == Type::OffsetBot ? 0 : 1);
  auto is_not_result = [&](const Compile::AliasType* alias_class) {
    if (alias_class->adr_type() == nullptr || !alias_class->adr_type()->isa_oopptr()) {
      return true;
    }
    const TypeOopPtr* alias_class_ptr = alias_class->adr_type()->is_oopptr();
    if (alias_class_ptr == TypeOopPtr::BOTTOM || alias_class_ptr == TypeInstPtr::MARK ||
        alias_class_ptr == TypeInstPtr::KLASS || alias_class_ptr == TypeAryPtr::RANGE) {
      return true;
    }

    MemorySlice alias_class_slice(alias_class_ptr->with_offset(0), alias_class_ptr->offset(), alias_class->_size);
    bool not_overlap = MemorySlice::not_overlap(alias_class_slice, ptr_slice);
#ifdef ASSERT
    if (!(not_overlap || MemorySlice::combine(alias_class_slice, ptr_slice) == alias_class_slice)) {
      stringStream ss;
      ss.print("(");
      alias_class_slice._base->dump_on(&ss);
      ss.print(", %d, %d) and (", alias_class_slice._offset, alias_class_slice._size);
      ptr_slice._base->dump_on(&ss);
      ss.print(", %d, %d)", ptr_slice._offset, ptr_slice._size);
      assert(false, "alias_slice cannot partially overlap ptr_slice: %s", ss.as_string());
    }
#endif // ASSERT
    return not_overlap;
  };

  for (int i = 0; i < C->num_alias_types(); i++) {
    Compile::AliasType* alias_class = C->alias_type(i);
    if (is_not_result(alias_class)) {
      continue;
    }

#ifdef ASSERT
    for (int j = i + 1; j < C->num_alias_types(); j++) {
      const Compile::AliasType* other_class = C->alias_type(j);
      if (!is_not_result(other_class)) {
        stringStream ptr_ss;
        ptr->dump_on(&ptr_ss);
        stringStream alias_ss;
        alias_class->adr_type()->dump_on(&alias_ss);
        stringStream other_ss;
        other_class->adr_type()->dump_on(&other_ss);
        assert(false, "must only find 1 AliasType for %s, found: [%s, %d], [%s, %d]",
               ptr_ss.as_string(true), alias_ss.as_string(true), alias_class->_size, other_ss.as_string(true), other_class->_size);
      }
    }
#endif // ASSERT

    return alias_class->adr_type()->is_oopptr();
  }

#ifdef ASSERT
  stringStream ss;
  ptr->dump_on(&ss);
  assert(false, "must find an AliasType for %s", ss.as_string(true));
#endif // ASSERT
  ShouldNotReachHere();
}

PhaseAliasAnalysis::PhaseAliasAnalysis(AliasAnalyzer& analyzer, PhaseIterGVN& igvn)
  : Phase(AliasAnalysis), _analyzer(analyzer), _igvn(igvn),
    _old_oop_alias_idx(C->have_alias_type(TypeOopPtr::BOTTOM) ? C->get_alias_index(TypeOopPtr::BOTTOM) : -1),
    _old_alias_limit(C->num_alias_types()), _memory_slices(nullptr), _old_nodes(nullptr), _merge_mems(nullptr), _old_phis_narrow_projs(nullptr) {}

void PhaseAliasAnalysis::optimize() {
  if (VerifyAliasAnalysis) {
    verify_graph();
  }

  if (_old_oop_alias_idx == -1) {
    // No heap access
    return;
  }

  {
    ResourceMark rm;
    GrowableArray<AliasAnalyzer::MemorySlice> memory_slices;
    Unique_Node_List old_nodes;
    Unique_Node_List merge_mems;
    Unique_Node_List old_phis_narrow_projs;
    _memory_slices = &memory_slices;
    _old_nodes = &old_nodes;
    _merge_mems = &merge_mems;
    _old_phis_narrow_projs = &old_phis_narrow_projs;

    analyze();
    do_transform();
    if (C->failing()) {
      return;
    }

    assert(_old_alias_limit + _memory_slices->length() == C->num_alias_types(), "unexpected number of alias classes");
    _memory_slices = nullptr;
    _old_nodes = nullptr;
    _merge_mems = nullptr;
    _old_phis_narrow_projs = nullptr;
  }

  _igvn.optimize();

  if (VerifyAliasAnalysis) {
    verify_graph();
  }
}

// Visit the whole graph, find all heap accesses, and divide them into slices
void PhaseAliasAnalysis::analyze() {
  RootNode* root = C->root();
  _old_nodes->push(root);
  for (uint i = 0; i < _old_nodes->size(); i++) {
    Node* n = _old_nodes->at(i);
    if (n->is_LoadStore()) {
      const TypePtr* adr_type = get_adr_type(n);
      assert(adr_type != nullptr, "must have memory");
      if (C->get_alias_index(adr_type) == _old_oop_alias_idx) {
        AliasAnalyzer::MemorySlice slice = heap_access_slice(adr_type->is_oopptr(), 1);
        add_slice(*_memory_slices, slice);
      }
    } else if (n->is_Mem()) {
      assert(n->adr_type() != nullptr, "must have memory");
      if (C->get_alias_index(n->adr_type()) == _old_oop_alias_idx) {
        AliasAnalyzer::MemorySlice slice = heap_access_slice(n->adr_type()->is_oopptr(), n->as_Mem()->memory_size());
        add_slice(*_memory_slices, slice);
      }
    } else if (n->Opcode() == Op_SCMemProj) {
      assert(n->adr_type() != nullptr, "must have memory");
      if (C->get_alias_index(n->adr_type()) == _old_oop_alias_idx) {
        AliasAnalyzer::MemorySlice slice = heap_access_slice(n->adr_type()->is_oopptr(), 1);
        add_slice(*_memory_slices, slice);
      }
    } else if (n->is_NarrowMemProj()) {
      assert(n->adr_type() != nullptr, "must have memory");
      if (C->get_alias_index(n->adr_type()) == _old_oop_alias_idx) {
        NarrowMemProjNode* narrow_mem = n->as_NarrowMemProj();
        auto process_narrow_proj_slice = [&](const AliasAnalyzer::MemorySlice& slice) {
          add_slice(*_memory_slices, slice);
        };
        for_each_narrow_mem_proj_slice(process_narrow_proj_slice, narrow_mem);
        _old_phis_narrow_projs->push(n);
      }
    } else if (n->is_MergeMem()) {
      MergeMemNode* mm = n->as_MergeMem();
      if (mm->memory_at(_old_oop_alias_idx) != mm->base_memory()) {
        _merge_mems->push(mm);
      }
    } else if (n->is_Phi()) {
      if (n->bottom_type() == Type::MEMORY && C->get_alias_index(n->adr_type()) == _old_oop_alias_idx) {
        _old_phis_narrow_projs->push(n);
      }
    } else if (n->is_ArrayCopy()) {
      // Macro expansion will try to extract finer memory slices for ArrayCopy
      ArrayCopyNode* ac = n->as_ArrayCopy();
      const TypeOopPtr* ptr = ac->_dest_type;
      if (ptr == TypeOopPtr::BOTTOM) {
        ptr = _igvn.type(n->in(ArrayCopyNode::Dest))->isa_oopptr();
      }
      if (ptr != nullptr) {
        if (ptr->isa_aryptr()) {
          const TypeAryPtr* aryptr = ptr->is_aryptr();
          if (aryptr->elem()->make_oopptr() != nullptr) {
            // Oop arrays, conservatively use the non-exact Object[], this will make all oop arrays
            // share the same alias class
            add_slice(*_memory_slices, heap_access_slice(TypeAryPtr::OOPS, 0));
          } else {
            // Primitive arrays each has its own exact slice
            add_slice(*_memory_slices, heap_access_slice(aryptr->with_offset(Type::OffsetBot), 0));
          }
        } else {
          ciInstanceKlass* klass = ptr->is_instptr()->instance_klass();
          const TypeOopPtr* base_adr_type = TypeOopPtr::make_from_klass(klass);
          for (int i = 0; i < klass->nof_nonstatic_fields(); i++) {
            ciField* field = klass->nonstatic_field_at(i);
            add_slice(*_memory_slices, heap_access_slice(base_adr_type->with_offset(field->offset_in_bytes()), field->size_in_bytes()));
          }
        }
      }
    } else {
      if (C->get_alias_index(n->adr_type()) == _old_oop_alias_idx) {
        // intrinsics nodes
        const TypeAryPtr* ptr = n->adr_type()->isa_aryptr();
        assert(ptr != nullptr, "must be an array pointer for %s", n->Name());
        int offset = Type::OffsetBot;
        normalize_aryptr(ptr, offset);
        AliasAnalyzer::MemorySlice slice(ptr, offset, 0);
        add_slice(*_memory_slices, slice);
      }
    }

    for (uint j = 0; j < n->req(); j++) {
      Node* m = n->in(j);
      if (m != nullptr) {
        _old_nodes->push(m);
      }
    }
  }

  verify_slices(*_memory_slices);
}

// Add a new slice s0 into a list of non-overlapping slices in a way that the result is also a list
// of non-overlapping slices. If s0 overlaps with an existing slice s1, we remove s1 from the list
// and try to add the slice s2 that is the union of the s0 and s1. Continue this process until we
// have a slice that does not overlap with any of the remaining slices in the list. It is entirely
// possible that we end up with a single slice that represents the whole heap.
void PhaseAliasAnalysis::add_slice(GrowableArray<AliasAnalyzer::MemorySlice>& current_slices, AliasAnalyzer::MemorySlice new_slice) {
  if (should_not_try_analyze(new_slice._base->with_offset(new_slice._offset))) {
    return;
  }

  // Whether new_slice does not overlap with any of the current_slices
  bool no_overlap = true;

  while (true) {
    // Whether we need to traverse current_slices another time because new_slice changed
    bool no_change = true;
    for (int i = 0; i < current_slices.length(); i++) {
      const AliasAnalyzer::MemorySlice& slice = current_slices.at(i);
      if (slice == new_slice) {
        // Already exist, nothing to do
        return;
      }

      if (AliasAnalyzer::MemorySlice::not_overlap(slice, new_slice)) {
        continue;
      }

      no_overlap = false;
      AliasAnalyzer::MemorySlice combined_slice = AliasAnalyzer::MemorySlice::combine(slice, new_slice);
      if (slice == combined_slice) {
        // There is a slice in the list that contains new_slice, there is also nothing to do
        return;
      }

      if (new_slice == combined_slice) {
        continue;
      }

      // If new_slice changes because it is combined with slice, we need to traverse the list
      // another time because combined_slice can overlap with a slice that new_slice does not
      new_slice = combined_slice;
      no_change = false;
    }

    if (no_change) {
      break;
    }
  }

  // Nothing overlaps with new_slice, we don't need to remove existing slices
  if (no_overlap) {
    current_slices.push(new_slice);
    return;
  }

  for (int i = current_slices.length() - 1; i >= 0; i--) {
    const AliasAnalyzer::MemorySlice& slice = current_slices.at(i);
    if (AliasAnalyzer::MemorySlice::not_overlap(slice, new_slice)) {
      continue;
    }

    assert(AliasAnalyzer::MemorySlice::combine(slice, new_slice) == new_slice, "new slice must contains removed slice");
    current_slices.delete_at(i);
  }

  current_slices.push(new_slice);
}

// Verify that all slices in the list are mutually non-overlapping
void PhaseAliasAnalysis::verify_slices(const GrowableArray<AliasAnalyzer::MemorySlice>& memory_slices) {
#ifdef ASSERT
  // We may find no heap access even if there is a slice for TypeOopPtr::BOTTOM, this is the case
  // if a MergeMemNode uses a TypePtr::BOTTOM for the heap access slice
  for (int i = 0; i < memory_slices.length(); i++) {
    const AliasAnalyzer::MemorySlice& this_slice = memory_slices.at(i);
    assert(!should_not_try_analyze(this_slice._base->with_offset(this_slice._offset)),
           "no slice with OffsetBot into an object");
    for (int j = i + 1; j < memory_slices.length(); j++) {
      assert(AliasAnalyzer::MemorySlice::not_overlap(this_slice, memory_slices.at(j)), "must always consists of non-overlapping slices");
    }
  }
#endif // ASSERT
}

void PhaseAliasAnalysis::do_transform() {
  if (check_node_limit()) {
    return;
  }

  create_alias_classes();
  _analyzer._analyzed = true;
  C->clear_alias_cache();
  split_memory_graph();

  // Agressively remove all old nodes that were split, this ensures that the old slice gets removed
  // completely from the graph
  for (uint i = 0; i < _old_phis_narrow_projs->size(); i++) {
    _igvn.remove_globally_dead_node(_old_phis_narrow_projs->at(i));
  }
}

// Alias analysis will split the memory state, hence it creates additional memory nodes, we must
// decide if we have enough node budget to do so. This also records Phis and NarrowMemProjs that
// need splitting.
bool PhaseAliasAnalysis::check_node_limit() {
  assert(!_analyzer._analyzed, "must happen before the alias class splitting");
  int additional_nodes = 0;
  for (uint i = 0; i < _old_phis_narrow_projs->size(); i++) {
    Node* current = _old_phis_narrow_projs->at(i);
    if (current->is_Phi()) {
      assert(current->bottom_type() == Type::MEMORY && C->get_alias_index(current->adr_type()) == _old_oop_alias_idx, "unexpected node");
      additional_nodes += _memory_slices->length();
    } else {
      assert(current->is_NarrowMemProj(), "unexpected node type %s", current->Name());
      assert(C->get_alias_index(current->adr_type()) == _old_oop_alias_idx, "unexpected node");
      bool is_exact;
      ciKlass* k = narrow_mem_alloc_klass(current->as_NarrowMemProj(), is_exact);
      if (k->is_array_klass()) {
        additional_nodes += 1;
      } else {
        // NarrowMemProj is expanded to one node for each field
        additional_nodes += k->as_instance_klass()->nof_nonstatic_fields();
      }
    }
  }

  return C->check_node_count(additional_nodes, "Insufficient node budget for alias analysis");
}

// Create a Compile::AliasType for each alias class that we have decided
void PhaseAliasAnalysis::create_alias_classes() {
  for (int i = 0; i < _memory_slices->length(); i++) {
    const AliasAnalyzer::MemorySlice& slice = _memory_slices->at(i);
    Compile::AliasType alias_class;
    alias_class.Init(C->num_alias_types(), slice._base->with_offset(slice._offset), slice._size);

    if (slice._base->isa_instptr()) {
      if (slice._offset != Type::OffsetBot) {
        ciInstanceKlass* klass = slice._base->is_instptr()->instance_klass();
        ciField* field = nullptr;
        if (klass == ciEnv::current()->Class_klass() && slice._base->const_oop() != nullptr && slice._offset > klass->layout_helper_size_in_bytes()) {
          // Static field
          ciKlass* field_holder = slice._base->const_oop()->as_instance()->java_lang_Class_klass();
          if (field_holder->is_instance_klass()) {
            field = field_holder->as_instance_klass()->get_field_by_offset(slice._offset, true);
          }
        } else {
          field = klass->get_field_by_offset(slice._offset, false);
        }

        if (field != nullptr && field->size_in_bytes() >= slice._size) {
          alias_class.set_field(field);
        }
      }
    } else {
      assert(slice._offset == Type::OffsetBot, "must be OffsetBot for arrays");
      alias_class._element = slice._base->is_aryptr()->elem();
    }

    C->add_alias_type(alias_class);
  }
}

void PhaseAliasAnalysis::split_memory_graph() {
#ifdef ASSERT
  assert(_analyzer._analyzed, "should have created new alias classes");
  for (uint i = 0; i < _old_nodes->size(); i++) {
    Node* n = _old_nodes->at(i);
    if (_old_phis_narrow_projs->member(n)) {
      continue;
    }
    const TypePtr* adr_type = get_adr_type(n);
    if (adr_type != nullptr && should_not_try_analyze(adr_type)) {
      continue;
    }

    assert(C->get_alias_index(get_adr_type(n)) != _old_oop_alias_idx, "no surviving node should have the old alias idx");
  }
#endif

  ResourceMark rm;
  SplitMemoryGraphData data(*this);
  
  // First, clone the Phis and NarrowMemProjs and record them in memory_states
  split_memory_nodes(data);

  // Follow the memory graph to find the new memory input for each node that consumes memory
  record_memory_edges(data);

  // Fix the graph to conform with the new alias classes
  fix_memory_edges(data);
}

void PhaseAliasAnalysis::split_memory_nodes(SplitMemoryGraphData& data) {
  for (uint idx = 0; idx < _old_phis_narrow_projs->size(); idx++) {
    Node* n = _old_phis_narrow_projs->at(idx);
    if (n->is_Phi()) {
      // Create a new Phi for each newly created alias class
      PhiNode* phi = n->as_Phi();
      Node** alias_states = NEW_RESOURCE_ARRAY(Node*, C->num_alias_types());
      std::memset(alias_states, 0, sizeof(Node*) * C->num_alias_types());
      data.split_mem_nodes.at_grow(phi->_idx) = alias_states;
      for (int i = 0; i < _memory_slices->length(); i++) {
        const AliasAnalyzer::MemorySlice& alias_slice = _memory_slices->at(i);
        const TypeOopPtr* alias_adr_type = alias_slice._base->with_offset(alias_slice._offset);
        PhiNode* new_phi = new PhiNode(phi->region(), Type::MEMORY, alias_adr_type);
        _igvn.register_new_node_with_optimizer(new_phi);
        int alias_idx = C->get_alias_index(alias_adr_type);
        alias_states[alias_idx] = new_phi;
      }
    } else {
      // Create a new NarrowMemProj for each alias class that the InitializeNode covers
      NarrowMemProjNode* narrow_proj = n->as_NarrowMemProj();
      Node** alias_states = NEW_RESOURCE_ARRAY(Node*, C->num_alias_types());
      std::memset(alias_states, 0, sizeof(Node*) * C->num_alias_types());
      data.split_mem_nodes.at_grow(narrow_proj->_idx) = alias_states;

      bool is_exact;
      ciKlass* k = narrow_mem_alloc_klass(narrow_proj, is_exact);
      const TypePtr* base_type = TypeOopPtr::make_from_klass(k, Type::trust_interfaces)->cast_to_exactness(is_exact);
      if (k->is_array_klass()) {
        const TypePtr* adr_type = base_type->with_offset(Type::OffsetBot);
        int alias_idx = C->get_alias_index(adr_type);
        const TypePtr* alias_adr_type = C->get_adr_type(alias_idx);
        NarrowMemProjNode* new_narrow_proj = new NarrowMemProjNode(narrow_proj->in(0)->as_Initialize(), alias_adr_type);
        _igvn.register_new_node_with_optimizer(new_narrow_proj);
        alias_states[alias_idx] = new_narrow_proj;
      } else {
        ciInstanceKlass* ik = k->as_instance_klass();
        for (int i = 0; i < ik->nof_nonstatic_fields(); i++) {
          ciField* field = ik->nonstatic_field_at(i);
          const TypePtr* adr_type = base_type->with_offset(field->offset_in_bytes());
          int alias_idx = C->get_alias_index(adr_type);
          const TypePtr* alias_adr_type = C->get_adr_type(alias_idx);
          NarrowMemProjNode* new_narrow_proj = new NarrowMemProjNode(narrow_proj->in(0)->as_Initialize(), alias_adr_type);
          _igvn.register_new_node_with_optimizer(new_narrow_proj);
          alias_states[alias_idx] = new_narrow_proj;
        }
      }
    }
  }
}

// Follow the memory graph and record the new memory input for each node, this also fixes the
// inputs of MergeMemNodes and adds inputs to the Phis created in split_memory_nodes
void PhaseAliasAnalysis::record_memory_edges(SplitMemoryGraphData& data) {
  int verify_inputs_size = VerifyAliasAnalysis ? C->num_alias_types() : 0;
  GrowableArray<Node*> verify_inputs(verify_inputs_size, verify_inputs_size, nullptr);

  // First, start from the MergeMemNodes, record the new memory inputs from uses to defs
  for (uint i = 0; i < _merge_mems->size(); i++) {
    MergeMemNode* mm = _merge_mems->at(i)->as_MergeMem();
    Node* input = mm->memory_at(_old_oop_alias_idx);
    assert(input != mm->base_memory(), "should not process this node");

    if (false) {
      for (int alias_idx = _old_alias_limit; alias_idx < C->num_alias_types(); i++) {
        verify_inputs.at(alias_idx) = find_new_memory_input(data, mm->memory_at(_old_oop_alias_idx), alias_idx);
      }
    }

    _igvn.rehash_node_delayed(mm);
    auto merge_mem_fix = [&](int alias_idx, Node* alias_state) {
      mm->set_memory_at(alias_idx, alias_state);
    };
    record_memory_edges_from_states(merge_mem_fix, data, input);
    mm->set_req_X(_old_oop_alias_idx, C->top(), &_igvn);

    if (false) {
      for (int alias_idx = _old_alias_limit; alias_idx < C->num_alias_types(); alias_idx++) {
        assert(mm->memory_at(alias_idx) == verify_inputs.at(alias_idx), "must match");
      }
    }
  }

  // Next, start from each of the inputs of Phis
  for (uint i = 0; i < _old_phis_narrow_projs->size(); i++) {
    Node* n = _old_phis_narrow_projs->at(i);
    if (!n->is_Phi()) {
      continue;
    }

    Node** split_phis = data.split_mem_nodes.at(n->_idx);
    assert(split_phis != nullptr, "must have been split");
    for (uint in_idx = 1; in_idx < n->req(); in_idx++) {
      if (false) {
        for (int alias_idx = _old_alias_limit; alias_idx < C->num_alias_types(); alias_idx++) {
          verify_inputs.at(alias_idx) = find_new_memory_input(data, n->in(in_idx), alias_idx);
        }
      }

      auto phi_fix = [&](int alias_idx, Node* alias_state) {
        Node* split_phi = split_phis[alias_idx];
        assert(split_phi != nullptr, "must have been assigned");
        split_phi->init_req(in_idx, alias_state);
      };
      record_memory_edges_from_states(phi_fix, data, n->in(in_idx));

      if (false) {
        for (int alias_idx = _old_alias_limit; alias_idx < C->num_alias_types(); alias_idx++) {
          assert(split_phis[alias_idx]->in(in_idx) == verify_inputs.at(alias_idx), "must match");
        }
      }
    }
  }

  if (!VerifyAliasAnalysis) {
    return;
  }

  // Verify the correctness of the algorithm using another approach. Traverse the whole graph to
  // find all nodes that consume _old_oop_alias_idx, then walk back along their memory input to
  // find the new memory input, verify that the 2 approaches give the same results.
  for (uint i = 0; i < _old_nodes->size(); i++) {
    Node* n = _old_nodes->at(i);
    if (n->is_Proj()) {
      assert(int(n->_idx) >= data.memory_inputs.length() || data.memory_inputs.at(n->_idx) == nullptr, "cannot change the input of a Proj");
      continue;
    }

    if (_old_phis_narrow_projs->member(n)) {
      assert(int(n->_idx) >= data.memory_inputs.length() || data.memory_inputs.at(n->_idx) == nullptr, "these nodes are killed");
      continue;
    }

    int alias_idx = C->get_alias_index(get_adr_type(n));
    if (alias_idx < _old_alias_limit) {
      assert(int(n->_idx) >= data.memory_inputs.length() || data.memory_inputs.at(n->_idx) == nullptr, "cannot change the memory of a non-oop access");
      continue;
    }

    // Walk back the memory graph to find a suitable input
    Node* old_in = n->in(memory_input_idx(n));
    Node* new_in = find_new_memory_input(data, old_in, alias_idx);
    assert(new_in == old_in || data.memory_inputs.at(n->_idx) == new_in, "must match");
  }
}

// Use memory_inputs to update the edges of other nodes
void PhaseAliasAnalysis::fix_memory_edges(const SplitMemoryGraphData& data) {
  // Fast path, no heap write in the compilation unit
  if (data.memory_inputs.is_empty()) {
    return;
  }

  for (uint i = 0; i < _old_nodes->size(); i++) {
    Node* n = _old_nodes->at(i);
    if (int(n->_idx) >= data.memory_inputs.length()) {
      continue;
    }

    Node* new_mem_in = data.memory_inputs.at(n->_idx);
    if (new_mem_in != nullptr) {
      int mem_in_idx = memory_input_idx(n);
      if (n->in(mem_in_idx) != new_mem_in) {
        _igvn.rehash_node_delayed(n);
        n->set_req_X(mem_in_idx, new_mem_in, &_igvn);
      }
    }
  }
}

static void do_nothing(int, Node*) {}

// Start from a node with complete states of all alias classes (a MergeMem or a Phi of
// TypeOopPtr::BOTTOM), walk along the edges corresponding to _old_oop_alias_idx, push the nodes on
// work_stack on the way until we encounter a Phi or a MergeMem. Then, walk backward, along the
// way, update alias_states, and fill in memory_inputs, the states at start are fixed at the end.
// Since there can be multiple inputs to start, we pass in the input with which to follow instead.
// We cannot fix the edges yet because a memory node can be the memory input of multiple nodes, and
// changing its input will break the graph, prevent later iterations which may encounter the
// changed node from a different output.
template <class F>
void PhaseAliasAnalysis::record_memory_edges_from_states(F fix_states, SplitMemoryGraphData& data, Node* start_input) {
  assert(data.work_stack.is_empty(), "must start with an empty stack");

  // Walk from use to def until we hit a TypePtr::BOTTOM or TypeOopPtr::BOTTOM
  Node* current = start_input;
  while (true) {
    if (current->bottom_type() == Type::MEMORY) {
      // Do not try to ask for the alias_index of the old Phis and NarrowMemProjs that were split,
      // they are illegal now.
      if (_old_phis_narrow_projs->member(current)) {
        // Stop at the TypeOopPtr::BOTTOM Phi but not at NarrowMemProj, another invocation will
        // walk from the Phi
        if (current->is_Phi()) {
          break;
        }
      } else {
        // For some reasons, Raw can act like Bot. As Raw should normally not be an input of Oop,
        // this Raw must have been used as a Bot here.
        int current_alias_idx = C->get_alias_index(get_adr_type(current));
        if (current_alias_idx <= Compile::AliasIdxRaw) {
          // Stop at Parm, there is nothing before it
          if (current->is_Parm()) {
            break;
          }

          // We do not know how to walk pass Phis and MergeMems
          if (current->is_Phi() || current->is_MergeMem()) {
            break;
          }

          // There may be nodes behind a BotPTR without a MergeMem, for example
          // mem(oop) -> GetAndAddI(oop) -> SCMemProj(Bot). We need to walk past the Bot memory to
          // reach those nodes. But since the Bot memory resets alias_states, we don't need to walk
          // beyond it to know what the alias_states of the memory we have walked past. As a
          // result, if another invocation has visited those nodes, we can stop now.
          if (data.visited.test_set(current->_idx)) {
            break;
          }
        }
      }
    }

    data.work_stack.push(current);
    current = current->in(memory_input_idx(current));
  }

  // Fill alias_states with end, because we are at a TypePtr::BOTTOM or TypeOopPtr::BOTTOM, it
  // covers all the alias classes we are processing. This also overwrites all information from the
  // previous invocation of this function.
  Node* end = current;
  if (_old_phis_narrow_projs->member(end)) {
    assert(end->is_Phi(), "cannot stop at a NarrowMemProj");
    Node** end_alias_states = data.split_mem_nodes.at(end->_idx);
    assert(end_alias_states != nullptr, "must have been split");
    // A Phi has been split and has a separate Phi for each alias class
    for (int i = _old_alias_limit; i < C->num_alias_types(); i++) {
      Node* split_phi = end_alias_states[i];
      assert(split_phi != nullptr, "must have been assigned");
      data.alias_states.at(i) = split_phi;
    }
  } else {
    assert(end->bottom_type() == Type::MEMORY && C->get_alias_index(get_adr_type(end)) <= Compile::AliasIdxRaw, "must be a Bot memory");
    for (int i = _old_alias_limit; i < C->num_alias_types(); i++) {
      data.alias_states.at(i) = end;
    }
  }

  // Walk back the path we just walked by popping from the work stack, update alias_states and
  // memory_inputs along the way. The stack should contain the nodes from start up to current
  // excluding the 2 bounds. Start right at the node we just stopped, that means the top of the
  // work stack will be the second node we process here.
  int cur_alias_idx = C->get_alias_index(get_adr_type(current));
  while (true) {
    // Record the new memory inputs of the users of current
    if (current->bottom_type() == Type::MEMORY) {
      for (DUIterator_Fast imax, i = current->fast_outs(imax); i < imax; i++) {
        Node* out = current->fast_out(i);
        assert(!out->is_Proj(), "no Proj output for a memory node");
        if (out->is_MergeMem() || out->is_Phi()) {
          // MergeMems and Phis are not handled here
          continue;
        }

        int out_alias_idx = C->get_alias_index(get_adr_type(out));
        if (cur_alias_idx <= Compile::AliasIdxRaw && out_alias_idx < _old_alias_limit) {
          // Since current is a bottom memory, a lot of nodes can be its outputs, so we keep the
          // assert out_alias_idx >= _old_alias_limit for the cases where current is not a bottom
          // memory only
          assert(!_old_phis_narrow_projs->member(current), "outputs of these nodes must be fixed");
          continue;
        }

        int out_mem_in_idx = memory_input_idx(out);
        if (out->in(out_mem_in_idx) != current) {
          // Not the memory input
          assert(!_old_phis_narrow_projs->member(current), "outputs of these nodes must be fixed");
          continue;
        }

        assert(out_alias_idx >= _old_alias_limit, "must be a new alias class");
        Node* new_in = data.alias_states.at(out_alias_idx);
        assert(new_in != nullptr, "must have a node");
        data.memory_inputs.at_grow(out->_idx) = new_in;
      }
    }

    // Process alias_states for the next node
    if (data.work_stack.is_empty()) {
      break;
    }
    current = data.work_stack.pop();
    if (current->is_NarrowMemProj()) {
      // NarrowMemProj sets multiple alias classes
      Node** current_split_nodes = data.split_mem_nodes.at(current->_idx);
      assert(current_split_nodes != nullptr, "must have been split");
      for (int i = _old_alias_limit; i < C->num_alias_types(); i++) {
        if (current_split_nodes[i] != nullptr) {
          data.alias_states.at(i) = current_split_nodes[i];
        }
      }
      // This value is to decide whether current is a Bot memory only
      cur_alias_idx = C->num_alias_types();
    } else if (current->bottom_type() == Type::MEMORY) {
      const TypePtr* adr_type = get_adr_type(current);
      cur_alias_idx = C->get_alias_index(adr_type);
      if (cur_alias_idx <= Compile::AliasIdxRaw) {
        // A Bot memory
        assert(data.visited.test(current->_idx), "must be a Bot memory we walked past");
        for (int i = _old_alias_limit; i < C->num_alias_types(); i++) {
          data.alias_states.at(i) = current;
        }
      } else if (cur_alias_idx < _old_alias_limit) {
        assert(should_not_try_analyze(adr_type), "must be a new alias class, unless we give up");
      } else {
        data.alias_states.at(cur_alias_idx) = current;
      }
    }
  }

  // Fix the inputs of starts
  for (int i = _old_alias_limit; i < C->num_alias_types(); i++) {
    fix_states(i, data.alias_states.at(i));
  }

  // If we stop because we don't know how to walk past end, we may need to solve it recursively, if
  // the node is in _old_phis_narrow_projs or _merge_mems, we need to fix its input, so we cannot
  // do it here
  if (end->is_Phi() && !_old_phis_narrow_projs->member(end)) {
    // Walk past a bottom Phi if it has not been visited yet
    if (!data.visited.test_set(end->_idx)) {
      for (uint i = 1; i < end->req(); i++) {
        record_memory_edges_from_states(do_nothing, data, end->in(i));
      }
    }
  } else if (end->is_MergeMem() && !_merge_mems->member(end)) {
    // A MergeMem that does not need fixing its inputs
    if (!data.visited.test_set(end->_idx)) {
      record_memory_edges_from_states(do_nothing, data, end->as_MergeMem()->base_memory());
    }
  }
}

// Get the index of the alias class from the memory slice of that alias class
int PhaseAliasAnalysis::alias_index(const AliasAnalyzer::MemorySlice& alias_slice) {
  assert(_analyzer._analyzed, "must be after splitting alias classes");
  const TypeOopPtr* alias_adr_type = alias_slice._base->with_offset(alias_slice._offset);
  int alias_idx = C->get_alias_index(alias_adr_type);
  assert(C->get_adr_type(alias_idx) == alias_adr_type, "consistency");
  return alias_idx;
}

uint PhaseAliasAnalysis::memory_input_idx(Node* n) {
  if (n->is_LoadStore()) {
    return 1;
  } else if (n->is_Mem()) {
    return MemNode::Memory;
  } else if (n->is_Proj()) {
    return 0;
  } else if (n->bottom_type()->base() == Type::Tuple) {
    return TypeFunc::Memory;
  } else if (n->Opcode() == Op_StrComp || n->Opcode() == Op_StrCompressedCopy || n->Opcode() == Op_StrInflatedCopy ||
             n->Opcode() == Op_StrEquals || n->Opcode() == Op_StrIndexOf || n->Opcode() == Op_StrIndexOfChar ||
             n->Opcode() == Op_AryEq || n->Opcode() == Op_CountPositives || n->Opcode() == Op_VectorizedHashCode ||
             n->Opcode() == Op_EncodeISOArray) {
    return 1;
  } else {
    assert(false, "unexpected node type %s", n->Name());
    ShouldNotReachHere();
  }
}

const TypePtr* PhaseAliasAnalysis::get_adr_type(Node* n) {
  const TypePtr* adr_type = n->adr_type();
  if (n->is_LoadStore() && adr_type == nullptr) {
    // This node lies about its adr_type
    Node* adr = n->in(2);
    adr_type = adr->bottom_type()->is_ptr();
  }
  return adr_type;
}

// Construct a memory slice corresponding to a heap access, normalize the ptr to a certain degree
AliasAnalyzer::MemorySlice PhaseAliasAnalysis::heap_access_slice(const TypeOopPtr* ptr, int memory_size) {
  assert(ptr != nullptr, "must access memory");
  int offset = ptr->offset();
  ptr = ptr->with_offset(0)->remove_speculative();

  if (ptr->isa_instptr()) {
    // Change NotNull to BotPTR
    const TypeInstPtr* instptr = ptr->is_instptr();
    TypePtr::PTR ptr_type = instptr->ptr() == TypePtr::NotNull ? TypePtr::BotPTR : instptr->ptr();
    ptr = TypeInstPtr::make(ptr_type, instptr->instance_klass(), instptr->interfaces(),
                               instptr->klass_is_exact(), instptr->const_oop(), 0);
  } else {
    const TypeAryPtr* aryptr = ptr->is_aryptr();
    normalize_aryptr(aryptr, offset);
    ptr = aryptr;
  }

  int size = offset == Type::OffsetBot ? 0 : memory_size;
  return AliasAnalyzer::MemorySlice(ptr, offset, size);
}

void PhaseAliasAnalysis::normalize_aryptr(const TypeAryPtr*& ptr, int& offset) {
  // The whole array body aliases as one
  offset = Type::OffsetBot;

  // Normalize element type to the widest
  const Type* elem = ptr->elem();
  if (elem->make_oopptr() != nullptr) {
    elem = elem->make_oopptr()->as_klass_type(false)->as_instance_type(false)->cast_to_exactness(false);
  } else if (elem != Type::BOTTOM) {
    elem = Type::get_const_basic_type(ptr->exact_klass()->as_type_array_klass()->element_type());
  }

  // Remove size, stability
  const TypeAry* ary = TypeAry::make(elem, TypeInt::POS, false);
  // Change NotNull to BotPTR
  TypePtr::PTR ptr_type = ptr->ptr() == TypePtr::NotNull ? TypePtr::BotPTR : ptr->ptr();
  if (elem->isa_oopptr() || elem == Type::BOTTOM) {
    // oop arrays or bottom arrays (e.g. meet of an int[] and a byte[])
    ptr = TypeAryPtr::make(ptr_type, ptr->const_oop(), ary, nullptr, ptr->klass_is_exact(), 0);
  } else {
    // primitive arrays
    ptr = TypeAryPtr::make(ptr_type, ptr->const_oop(), ary, ptr->exact_klass(), true, 0);
  }
}

template <class F>
void PhaseAliasAnalysis::for_each_narrow_mem_proj_slice(F f, NarrowMemProjNode* node) {
  bool is_exact;
  ciKlass* k = narrow_mem_alloc_klass(node, is_exact);
  const TypeOopPtr* ptr = TypeOopPtr::make_from_klass(k, Type::trust_interfaces)->cast_to_exactness(is_exact);
  if (k->is_array_klass()) {
    const TypeAryPtr* aryptr = ptr->is_aryptr();
    int offset = Type::OffsetBot;
    normalize_aryptr(aryptr, offset);
    f(AliasAnalyzer::MemorySlice(aryptr, offset, 0));
  } else {
    ciInstanceKlass* ik = k->as_instance_klass();
    for (int i = 0; i < ik->nof_nonstatic_fields(); i++) {
      ciField* field = ik->nonstatic_field_at(i);
      f(AliasAnalyzer::MemorySlice(ptr, field->offset_in_bytes(), field->size_in_bytes()));
    }
  }
}

ciKlass* PhaseAliasAnalysis::narrow_mem_alloc_klass(NarrowMemProjNode* node, bool& is_exact) {
  assert(node->in(0) != nullptr, "Proj with no input at 0");
  assert(node->in(0)->is_Initialize(), "unexpected node type %s", node->in(0)->Name());
  InitializeNode* init = node->in(0)->as_Initialize();
  AllocateNode* alloc = init->allocation();
  assert(alloc != nullptr, "must have a corresponding allocation");
  Node* klass_node = alloc->in(AllocateNode::KlassNode);
  assert(klass_node != nullptr, "AllocateNode must have a klass node");
  const TypeKlassPtr* klass_type = _igvn.type(klass_node)->isa_klassptr();
  assert(klass_type != nullptr, "must be a klass pointer");
  if (klass_type->klass_is_exact()) {
    is_exact = true;
    return klass_type->exact_klass();
  } else {
    is_exact = false;
    return klass_type->cast_to_exactness(true)->exact_klass();
  }
}

AliasAnalyzer::MemorySlice::MemorySlice(const TypeOopPtr* base, int offset, int size) : _base(base), _offset(offset), _size(size) {
  assert(base->offset() == 0, "base must not have offset");
  assert(offset == Type::OffsetBot || offset > 0, "invalid offset %d", offset);
  assert((offset != Type::OffsetBot && size > 0) || (offset == Type::OffsetBot && size == 0), "OffsetBot iff size 0");
}

// Decide if 2 MemorySlice overlap with each other
bool AliasAnalyzer::MemorySlice::not_overlap(const MemorySlice& x, const MemorySlice& y) {
  if ((x._base->is_known_instance() || y._base->is_known_instance()) && x._base != y._base) {
    // Known instances only alias with themselves
    return true;
  }

  const Type* base = x._base->join(y._base);
  if (base->empty() || !base->isa_oopptr()) {
    // Base can only intersect at null
    return true;
  }

  if (x._offset == Type::OffsetBot || y._offset == Type::OffsetBot) {
    return false;
  }

  // Invariant size > 0
  int limit_x = x._offset + x._size;
  int limit_y = y._offset + y._size;
  // Test for interval overlap:
  // Suppose there exists a value v such that:
  //   x._offset <= v < limit_x
  //   y._offset <= v < limit_y
  // This means x._offset <= v < limit_y && y._offset <= v < limit_x
  //
  // The reverse is also true, if x._offset < limit_y && y._offset < limit_x:
  // WLOG x._offset <= y._offset, we have y._offset being a value belong to both intervals
  // Since this method tests if 2 intervals do not overlap, the boolean is negated.
  return x._offset >= limit_y || y._offset >= limit_x;
}

// Construct the union of 2 MemorySlices, this action is conservative, the combined slice must
// contains both input slices, but it can also contains memory location not in either of the input
// slices.
AliasAnalyzer::MemorySlice AliasAnalyzer::MemorySlice::combine(const MemorySlice& x, const MemorySlice& y) {
  const TypeOopPtr* base = x._base->meet(y._base)->is_oopptr();
  if (x._offset == Type::OffsetBot || y._offset == Type::OffsetBot) {
    return MemorySlice(base, Type::OffsetBot, 0);
  } else {
    // Union of 2 intervals
    int limit_x = x._offset + x._size;
    int limit_y = y._offset + y._size;
    int limit = MAX2(limit_x, limit_y);
    int offset = MIN2(x._offset, y._offset);
    int size = limit - offset;
    return MemorySlice(base, offset, size);
  }
}

bool AliasAnalyzer::MemorySlice::operator==(const MemorySlice& o) const {
  return _base == o._base && _offset == o._offset && _size == o._size;
}

PhaseAliasAnalysis::SplitMemoryGraphData::SplitMemoryGraphData(PhaseAliasAnalysis& alias_analysis)
  : split_mem_nodes(alias_analysis._old_nodes->size()),
    memory_inputs(alias_analysis._old_nodes->size()),
    alias_states(alias_analysis.C->num_alias_types(), alias_analysis.C->num_alias_types(), nullptr),
    work_stack(), visited() {}

void PhaseAliasAnalysis::verify_graph() {
  // For some reasons, Raw can be used as Bot (e.g. GraphKit::set_output_for_allocation). As a
  // result, verification should be lenient between Bot and Raw.
  auto verify_node = [&](Node* n) {
    int n_alias_idx = C->get_alias_index(get_adr_type(n));
    if (n->is_Parm()) {
      // This is the start, there is no input to examine
      assert(n->bottom_type() != Type::MEMORY || n_alias_idx == Compile::AliasIdxBot, "Parm must be Bot %d", n_alias_idx);
      return;
    }
    if (n_alias_idx == Compile::AliasIdxTop) {
      return;
    }

    if (n->is_Phi()) {
      if (n->bottom_type() == Type::MEMORY) {
        for (uint i = 1; i < n->req(); i++) {
          int in_alias_idx = C->get_alias_index(get_adr_type(n->in(i)));
          assert(n_alias_idx == in_alias_idx || in_alias_idx <= Compile::AliasIdxRaw, "inputs of a Phi must match %d, %d", n_alias_idx, in_alias_idx);
        }
      }
      return;
    } else if (n->is_MergeMem()) {
      assert(get_adr_type(n) == TypePtr::BOTTOM, "must merge all memory");
      Node* base = n->as_MergeMem()->base_memory();
      int base_alias_idx = C->get_alias_index(get_adr_type(base));
      assert(base_alias_idx <= Compile::AliasIdxRaw, "base must be Bot or Raw %d", base_alias_idx);
      for (int i = Compile::AliasIdxRaw; i < C->num_alias_types(); i++) {
        Node* in = n->as_MergeMem()->memory_at(i);
        int in_alias_idx = C->get_alias_index(get_adr_type(in));
        assert(in_alias_idx == i || in_alias_idx <= Compile::AliasIdxRaw,
               "inputs of a MergeMem must match %d, %d", i, in_alias_idx);
      }
      return;
    }

    if (n->req() <= memory_input_idx(n)) {
      return;
    }

    Node* in = n->in(memory_input_idx(n));
    const TypePtr* in_adr_type = get_adr_type(in);
    int in_alias_idx = C->get_alias_index(in_adr_type);
    if (n_alias_idx <= Compile::AliasIdxRaw) {
      assert(in_alias_idx <= Compile::AliasIdxRaw || n->Opcode() == Op_SCMemProj ||
             (n->is_MemBar() && should_not_try_analyze(in_adr_type)),
             "unexpected case when a non-bottom is the input of a bottom %s, %s, %d", n->Name(), in->Name(), in_alias_idx);
    } else {
      assert(in_alias_idx <= Compile::AliasIdxRaw || in_alias_idx == n_alias_idx, "input of a memory consumer must match %d, %d", n_alias_idx, in_alias_idx);
    }
  };

  ResourceMark rm;
  Unique_Node_List wq;
  wq.push(C->root());
  for (uint i = 0; i < wq.size(); i++) {
    Node* n = wq.at(i);
    verify_node(n);
    for (uint j = 0; j < n->req(); j++) {
      Node* in = n->in(j);
      if (in != nullptr) {
        wq.push(in);
      }
    }
  }
}

Node* PhaseAliasAnalysis::find_new_memory_input(const SplitMemoryGraphData& data, Node* in, int alias_idx) {
  // Walk back the memory graph to find a suitable input
  Node* new_in = in;
  for (;; new_in = new_in->in(memory_input_idx(new_in))) {
    // The new input can be one we split in split_memory_nodes
    if (_old_phis_narrow_projs->member(new_in)) {
      if (new_in->is_Phi()) {
        Node** split_phis = data.split_mem_nodes.at(new_in->_idx);
        assert(split_phis != nullptr, "must have been split");
        new_in = split_phis[alias_idx];
        break;
      } else {
        Node** split_narrow_projs = data.split_mem_nodes.at(new_in->_idx);
        assert(split_narrow_projs != nullptr, "must have been split");
        Node* split_proj = split_narrow_projs[alias_idx];
        if (split_proj != nullptr) {
          new_in = split_proj;
          break;
        } else {
          continue;
        }
      }
    }

    // Bot or a matching alias class. For some reasons, Raw can act as a Bot. As normally Raw
    // should not be an input of Oop, this Raw is a Bot, so stop at Raw, too.
    if (new_in->bottom_type() == Type::MEMORY) {
      int in_alias_idx = C->get_alias_index(get_adr_type(new_in));
      if (in_alias_idx <= Compile::AliasIdxRaw || in_alias_idx == alias_idx) {
        break;
      }
    }
  }

  assert(new_in != nullptr, "must find an input");
  return new_in;
}
