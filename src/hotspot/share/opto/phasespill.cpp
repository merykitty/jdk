/*
 * Copyright (c) 2024, Oracle and/or its affiliates. All rights reserved.
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

#include "precompiled.hpp"
#include "opto/addnode.hpp"
#include "opto/block.hpp"
#include "opto/compile.hpp"
#include "opto/machnode.hpp"
#include "opto/loopnode.hpp"
#include "opto/phasespill.hpp"
#include "utilities/pair.hpp"

static uint find_first_node(const Block& b) {
  for (uint i = 1;; i++) {
    Node* n = b.get_node(i);
    if (!n->is_Proj() && !n->is_Phi()) {
      return i;
    }
    assert(n->in(0) == b.head(), "");
  }
}

static void calculate_liveout(const PhaseCFG& cfg,
                              GrowableArray<PhaseSpill::DistanceDatum>& liveout,
                              const GrowableArrayView<PhaseSpill::BlockInfo>& info,
                              Block& b) {
  // Loop exit is a very long edge, considering the control flow would loop
  // several times before actually exits
  constexpr int loop_base = 9;
  constexpr int loop_increment = 3;
  constexpr int loop_limit = 18;
  // For an uncommon branch, we only reload the value inside that branch,
  // leaving the common path untouched, this may lead to a greater distance
  constexpr double uncommon_threshold = 0.1;
  constexpr int uncommon_penalty = 1 << 7;
  constexpr double untaken_threshold = 0.001;
  constexpr int untaken_penalty = 1 << 21;

  for (uint succ_idx = 0; succ_idx < b._num_succs; succ_idx++) {
    Block* succ = b._succs[succ_idx];
    bool is_loop_exit = false;
    int block_distance = 0;
    if (succ->_loop->height() > b._loop->height()) {
      is_loop_exit = true;
      int distance_shift = MIN2(loop_base + loop_increment * b._loop->height(), loop_limit);
      block_distance = 1 << distance_shift;
    }
    double succ_prob = b.succ_prob(succ_idx);
    bool is_untaken = !is_loop_exit && succ_prob < untaken_threshold;
    bool is_uncommon = !is_loop_exit && !is_untaken && succ_prob < uncommon_threshold;

    uint this_idx;
    for (this_idx = 1;; this_idx++) {
      if (cfg.get_block_for_node(succ->pred(this_idx)) == &b) {
        break;
      }
    }

    const auto& succ_livein = info.at(succ->_rpo).livein();
    for (int i = 0; i < succ_livein.length(); i++) {
      Node* n = succ_livein.at(i).node;
      int distance = succ_livein.at(i).distance;
      int max_height = succ_livein.at(i).max_height;
      if (n->is_Phi() && n->in(0) == succ->head()) {
        n = n->in(this_idx);
        distance = 0;
        max_height = succ->_loop->height();
      }

      distance += block_distance;
      max_height = MAX2(max_height, b._loop->height());
      if (is_untaken) {
        distance += untaken_penalty;
        max_height = max_jint;
      } else if (is_uncommon) {
        distance += uncommon_penalty;
      }

      bool exist = false;
      for (int j = 0; j < liveout.length(); j++) {
        auto& f = liveout.at(j);
        if (f.node == n) {
          exist = true;
          f.distance = MIN2(f.distance, distance);
          f.max_height = MIN2(f.max_height, max_height);
          break;
        }
      }
      if (!exist) {
        liveout.append({n, distance, max_height});
      }
    }
  }
}

static void calculate_live(GrowableArray<PhaseSpill::DistanceDatum>& live,
                           const GrowableArrayView<PhaseSpill::DistanceDatum>& liveout,
                           const Block& b, uint idx) {
  GrowableArray<Node*> defs;
  int curr_distance = 0;
  for (uint i = idx; i < b.number_of_nodes(); i++) {
    Node* n = b.get_node(i);
    defs.append(n);
    if (n->is_Mach() && !n->is_MachTemp() && !n->is_Proj()) {
      curr_distance++;
    }
    for (uint j = 1; j < n->req(); j++) {
      Node* in = n->in(j);
      if (in == nullptr || defs.contains(in)) {
        continue;
      }
      bool exist = false;
      for (int k = 0; k < live.length(); k++) {
        if (live.at(k).node == in) {
          exist = true;
          break;
        }
      }
      if (!exist) {
        live.append({in, curr_distance, b._loop->height()});
      }
    }
  }

  for (int i = 0; i < liveout.length(); i++) {
    auto& e = liveout.at(i);
    if (defs.contains(e.node)) {
      continue;
    }
    bool exist = false;
    for (int j = 0; j < live.length(); j++) {
      if (live.at(j).node == e.node) {
        exist = true;
        break;
      }
    }
    if (!exist) {
      live.append({e.node, e.distance + curr_distance, e.max_height});
    }
  }
}

static bool equals(const GrowableArrayView<PhaseSpill::DistanceDatum>& a,
                   const GrowableArrayView<PhaseSpill::DistanceDatum>& b) {
#ifdef ASSERT
  for (int i = 0; i < a.length(); i++) {
    for (int j = i + 1; j < a.length(); j++) {
      assert(a.at(i).node != a.at(j).node, "");
    }
  }
  for (int i = 0; i < b.length(); i++) {
    for (int j = i + 1; j < b.length(); j++) {
      assert(b.at(i).node != b.at(j).node, "");
    }
  }
#endif // ASSERT

  if (a.length() != b.length()) {
    return false;
  }

  for (int i = 0; i < a.length(); i++) {
    bool found = false;
    auto& a_datum = a.at(i);
    for (int j = 0; j < b.length(); j++) {
      auto& b_datum = b.at(j);
      if (a_datum.node == b_datum.node) {
        found = a_datum.distance == b_datum.distance &&
                a_datum.max_height == b_datum.max_height;
        break;
      }
    }
    if (!found) {
      return false;
    }
  }
  return true;
}

static Node* find_base_for_derived(PhaseCFG& cfg, Node* machnull,
                                   GrowableArrayView<Node*>& derived_base_map, Node* derived) {
  // See if already computed; if so return it
  Node*& res = derived_base_map.at(derived->_idx);
  if (res != nullptr) {
    return res;
  }

#ifdef ASSERT
  if (derived->is_Mach() && derived->as_Mach()->ideal_Opcode() == Op_VerifyVectorAlignment) {
    // Bypass the verification node
    Node* base = find_base_for_derived(cfg, machnull, derived_base_map, derived->in(1));
    res = base;
    return base;
  }
#endif

  // See if this happens to be a base.
  // NOTE: we use TypePtr instead of TypeOopPtr because we can have
  // pointers derived from null! These are always along paths that
  // can't happen at run-time but the optimizer cannot deduce it so
  // we have to handle it gracefully.
  assert(!derived->bottom_type()->isa_narrowoop() ||
         derived->bottom_type()->make_ptr()->is_ptr()->offset() == 0, "sanity");
  const TypePtr* tj = derived->bottom_type()->isa_ptr();
  if (tj == nullptr || tj->offset() == 0) {
    res = derived;
    return derived;
  }

  // Derived is Con (null + Con)? Base is null!
  if (derived->is_Con()) {
    Node* base = machnull;
    if (cfg.get_block_for_node(machnull) == nullptr) {
      Node* top = cfg.C->top();
      Block& start = *cfg.get_block_for_node(top);
      assert(start._rpo == 1, "");
      uint insert_idx = start.find_node(top) + 1;
      start.insert_node(machnull, insert_idx);
      cfg.map_node_to_block(machnull, &start);

      for (DUIterator_Fast imax, i = machnull->fast_outs(imax); i < imax; i++) {
        Node* out = machnull->fast_out(i);
        if (!out->is_Proj()) {
          continue;
        }

        insert_idx++;
        start.insert_node(out, insert_idx);
        cfg.map_node_to_block(out, &start);
      }
    }

    res = base;
    return base;
  }

  // Check for AddP-related opcodes
  if (!derived->is_Phi()) {
    assert(derived->as_Mach()->ideal_Opcode() == Op_AddP, "but is: %s", derived->Name());
    Node* base = derived->in(AddPNode::Base);
    res = base;
    return base;
  }

  // Recursively find bases for Phis.
  // First check to see if we can avoid a base Phi here.
  Node* base = find_base_for_derived(cfg, machnull, derived_base_map, derived->in(1));
  assert(base != nullptr, "");
  for (uint i = 2; i < derived->req(); i++) {
    if (base != find_base_for_derived(cfg, machnull, derived_base_map, derived->in(i))) {
      base = nullptr;
      break;
    }
  }
  // Went to the end without finding any different bases?
  if (base != nullptr) {   // No need for a base Phi here
    res = base;
    return base;
  }

  // Now we see we need a base-Phi here to merge the bases
  const Type* t = Type::TOP;
  base = new PhiNode(derived->in(0), t);
  for (uint i = 1; i < derived->req(); i++) {
    base->init_req(i, find_base_for_derived(cfg, machnull, derived_base_map, derived->in(i)));
    t = t->meet(base->in(i)->bottom_type());
  }
  base->as_Phi()->set_type(t);

  // Search the current block for an existing base-Phi
  Block& b = *cfg.get_block_for_node(derived);
  for (uint i = 1; i <= b.end_idx(); i++) {
    Node* phi = b.get_node(i);
    if (!phi->is_Phi()) {      // Found end of Phis with no match?
      b.insert_node(base, i); // Must insert created Phi here as base
      cfg.map_node_to_block(base, &b);
      break;
    }
    // See if Phi matches.
    bool match = true;
    for (uint j = 1; j < base->req(); j++) {
      if (phi->in(j) != base->in(j)) {
        match = false;
        break;
      }
    }
    if (match) {
      base = phi;
      break;
    }
  }

  res = base;
  return base;
}

// For all derived pointers living across a safepoint, find their corresponding
// bases and append a pair of (derived, base) to the inputs of sft
static void map_derived_to_base(PhaseCFG& cfg, Node* machnull,
                                GrowableArrayView<Node*>& derived_base_map,
                                Node* sft, const GrowableArrayView<PhaseSpill::DistanceDatum>& live) {
  for (int i = 0; i < live.length(); i++) {
    auto& datum = live.at(i);
    Node* n = datum.node;
    if (n == sft) {
      continue;
    }
    const TypePtr* tp = n->bottom_type()->isa_oopptr();
    if (tp == nullptr || tp->offset() == 0) {
      continue;
    }

    Node* base = find_base_for_derived(cfg, machnull, derived_base_map, n);
    sft->add_req(n);
    sft->add_req(base);
  }
}

static void fixup_base_derived_map(Node* sft, const GrowableArrayView<PhaseSpill::DistanceDatum>& live,
                                   GrowableArray<Node*>& tmp1, GrowableArray<Node*>& tmp2) {
  // Look through all phis and copies to find the unique def if there is one
  auto get_def = [&](Node* n) {
    tmp1.clear();
    tmp2.clear();
    Node* def = nullptr;
    tmp1.append(n);
    while (tmp1.is_nonempty()) {
      Node* curr = tmp1.at(tmp1.length() - 1);
      tmp1.remove_at(tmp1.length() - 1);
      while (curr->is_MachSpillCopy()) {
        curr = curr->in(1);
      }
      if (!curr->is_Phi()) {
        if (def == nullptr) {
          def = curr;
        } else if (def != curr) {
          return n;
        }
        continue;
      }

      tmp2.append(curr);
      for (uint i = 1; i < curr->req(); i++) {
        Node* in = curr->in(i);
        if (!tmp2.contains(in)) {
          tmp1.append(in);
        }
      }
    }

    return def;
  };

  JVMState* jvms = sft->jvms();
  assert(jvms != nullptr, "");
  for (int node_idx = 0; node_idx < live.length(); node_idx++) {
    Node* n = live.at(node_idx).node;
    if (n == sft) {
      continue;
    }
    const TypePtr* tp = n->bottom_type()->isa_oopptr();
    if (tp == nullptr || tp->offset() == 0) {
      continue;
    }

    assert((sft->req() - jvms->oopoff()) % 2 == 0, "");
    bool found = false;
    Node* base = nullptr;
    for (uint i = jvms->oopoff(); i < sft->req(); i += 2) {
      Node* derived = sft->in(i);
      if (derived == n) {
        found = true;
        break;
      } else if (get_def(n) == get_def(derived)) {
        base = sft->in(i + 1);
      }
    }
    if (found) {
      continue;
    }

    assert(!n->as_MachSpillCopy()->out_RegMask().is_UP() &&
           get_def(n) == n->in(1), "");
    assert(base != nullptr, "");
    sft->add_req(n);
    sft->add_req(base);
  }
}

PhaseSpill::PhaseSpill(PhaseCFG& cfg)
  : Phase(Phase::Spill), _cfg(cfg), _arena(mtCompiler),
    _blocks(&_arena, cfg.number_of_blocks(), cfg.number_of_blocks(), nullptr),
    _live_info(&_arena, _blocks.length(), _blocks.length(), BlockInfo(_arena)),
    _limit_pressure(RegPressure::limit()),
    _spill_map(&_arena, C->unique(), C->unique(), nullptr),
    _spill_list(&_arena, 0, 0, nullptr),
    _reload_list(&_arena, 0, 0, nullptr) {
  ResourceMark rm;

  // Blocks in rpo
  for (uint idx = 0; idx < cfg.number_of_blocks(); idx++) {
    Block* b = cfg.get_block(idx);
    _blocks.at(b->_rpo) = b;
    _live_info.at(b->_rpo)._block = b;
  }
  compute_live();

  // At each Safepoint, insert extra debug edges for each pair of derived value/
  // base pointer that is live across the Safepoint for oopmap building.  The
  // edge pairs get added in after sfpt->jvmtail()->oopoff(), but are in the
  // required edge set.
  GrowableArray<DistanceDatum> live;
  GrowableArray<Node*> derived_base_map(C->unique(), C->unique(), nullptr);
  for (int block_idx = 0; block_idx < _blocks.length(); block_idx++) {
    const Block& block = *_blocks.at(block_idx);
    for (uint node_idx = 0; node_idx < block.number_of_nodes(); node_idx++) {
      Node* n = block.get_node(node_idx);
      JVMState* jvms = n->jvms();
      if (jvms == nullptr) {
        continue;
      }

      live.clear();
      calculate_live(live, _live_info.at(block_idx)._liveout, block, node_idx + 1);
      map_derived_to_base(_cfg, C->matcher()->mach_null(), derived_base_map, n, live);
    }
  }
}

void PhaseSpill::compute_live() {
  ResourceMark rm;

  for (int i = 0; i < _live_info.length(); i++) {
    auto& e = _live_info.at(i);
    e._livein.clear();
    e._liveout.clear();
    e._hrp = HighPressureInfo();
  }

  // livein and liveout
  GrowableArray<Block*> worklist(_blocks.length());
  assert(_blocks.at(0)->_rpo == 0, "");
  assert(_blocks.at(0)->head()->is_Root(), "");
  for (int i = _blocks.length() - 1; i > 0; i--) {
    Block* b = _blocks.at(i);
    assert(i == int(b->_rpo), "blocks must be in rpo");
    auto& info = _live_info.at(i);
    calculate_liveout(_cfg, info._liveout, _live_info, *b);
    calculate_live(info._livein, info._liveout, *b, find_first_node(*b));
  }
  for (int i = 1; i < _blocks.length(); i++) {
    worklist.append(_blocks.at(i));
  }

  GrowableArray<DistanceDatum> temp_liveout;
  while (worklist.is_nonempty()) {
    Block* b = worklist.at(worklist.length() - 1);
    worklist.remove_at(worklist.length() - 1);
    auto& info = _live_info.at(b->_rpo);
    temp_liveout.clear();
    calculate_liveout(_cfg, temp_liveout, _live_info, *b);
    bool changed = !equals(temp_liveout, info._liveout);
    if (!changed) {
      continue;
    }

    info._liveout.clear();
    info._liveout.appendAll(&temp_liveout);
    info._livein.clear();
    calculate_live(info._livein, info._liveout, *b, find_first_node(*b));
    for (uint i = 0; i < b->num_preds(); i++) {
      Block* pred = _cfg.get_block_for_node(b->pred(i));
      if (!pred->head()->is_Root()) {
        worklist.append_if_missing(pred);
      }
    }
  }
  assert(verify_live_info(), "");

  // Calculate max pressure
  GrowableArray<Node*> temp;
  for (int block_idx = 1; block_idx < _blocks.length(); block_idx++) {
    _live_info.at(block_idx).compute_max_pressure(_limit_pressure, temp);
  }
}

void PhaseSpill::do_spilling() {
  if (!should_spill()) {
    return;
  }

  ResourceMark rm;
  GrowableArray<DistanceDatum> live;
  compute_live();

#ifdef ASSERT
  int old_block_idx = -1;
  int old_hrp_idx = -1;
#endif // ASSERT
  while (true) {
    bool progress = false;
    for (int block_idx = 1; block_idx < _blocks.length(); block_idx++) {
      Block* block = _blocks.at(block_idx);
      BlockInfo& info = _live_info.at(block_idx);
      int hrp_idx = info._hrp.first_idx();
      if (hrp_idx == -1) {
        continue;
      }

      assert(block_idx > old_block_idx || (block_idx == old_block_idx && hrp_idx >= old_hrp_idx), "");
      progress = true;
      live.clear();
      calculate_live(live, info._liveout, *block, hrp_idx);
      // We need to spill before the register pressure is high
      // Find the place that has variables to spill, walk back the block past the
      // latest instruction
      int spill_idx = hrp_idx;
      while (true) {
        spill_idx--;
        Node* n = block->get_node(spill_idx);
        // This node cannot be spilt because when it is defined the pressure is
        // already too high
        for (int i = 0; i < live.length(); i++) {
          if (live.at(i).node == n) {
            live.remove_at(i);
          }
        }
        if (!n->is_Proj()) {
          break;
        }
      }
      assert(spill_idx >= int(find_first_node(*block)),
            "livein of the first high pressure block must not be high pressure");

      Node* spilt = nullptr;
      int max_max_height = -1;
      int max_distance = -1;
      for (int i = 0; i < live.length(); i++) {
        const auto& cand = live.at(i);
        Node* n = cand.node;
        if (n->is_MachTemp()) {
          continue;
        }
        if (!info._hrp.first_hrp().relieve_by(RegPressure(n), _limit_pressure)) {
          continue;
        }

        auto loop_lca = [](CFGLoop* l1, CFGLoop* l2) {
          while (l1->depth() > l2->depth()) {
            l1 = l1->parent();
          }
          while (l1->depth() < l2->depth()) {
            l2 = l2->parent();
          }
          while (l1 != l2) {
            l1 = l1->parent();
            l2 = l2->parent();
          }
          assert(l1 != nullptr, "");
          return l1;
        };

        bool has_spilt = _spill_map.at(n->_idx) != nullptr;
        int max_height = cand.max_height;
        int distance = cand.distance;
        if (has_spilt) {
          // Bias toward values that have already been on the stack
          distance *= 2;
        } else {
          // Take into consideration stores if we have to make them
          int def_max_height = loop_lca(_cfg.get_block_for_node(n)->_loop, block->_loop)->height();
          max_height = MIN2(def_max_height, max_height);
        }
        if (max_height > max_max_height) {
          max_max_height = max_height;
          max_distance = distance;
          spilt = n;
        } else if (max_height == max_max_height && distance > max_distance) {
          max_distance = distance;
          spilt = n;
        }
      }
      assert(spilt != nullptr, "");
      spill(spilt, *block, hrp_idx);
      compute_live();
#ifdef ASSERT
      live.clear();
      calculate_live(live, info._liveout, *block, hrp_idx);
      for (int i = 0; i < live.length(); i++) {
        assert(live.at(i).node != spilt, "");
      }
      old_block_idx = block_idx;
      old_hrp_idx = hrp_idx;
      _cfg.verify();
#endif
      break;
    }

    if (!progress) {
      break;
    }
  }

  GrowableArray<Node*> tmp1;
  GrowableArray<Node*> tmp2;
  for (int block_idx = 0; block_idx < _blocks.length(); block_idx++) {
    Block& block = *_blocks.at(block_idx);
    for (uint node_idx = 0; node_idx < block.number_of_nodes(); node_idx++) {
      Node* n = block.get_node(node_idx);
      JVMState* jvms = n->jvms();
      if (jvms == nullptr) {
        continue;
      }

      live.clear();
      calculate_live(live, _live_info.at(block_idx)._liveout, block, node_idx + 1);
      fixup_base_derived_map(n, live, tmp1, tmp2);
    }
  }

  // Use _reload_list as the worklist
  while (_reload_list.is_nonempty()) {
    Node* curr = _reload_list.at(_reload_list.length() - 1);
    _reload_list.remove_at(_reload_list.length() - 1);
    if (curr->outcnt() > 0) {
      continue;
    }

    Block* block = _cfg.get_block_for_node(curr);
    if (block == nullptr) {
      continue;
    }

    _cfg.unmap_node_from_block(curr);
    block->find_remove(curr);
    for (uint i = 1; i < curr->req(); i++) {
      assert(curr->in(i) != nullptr, "");
      _reload_list.append(curr->in(i));
    }
    curr->disconnect_inputs(C);
  }

  for (Node* spill : _spill_list) {
    Block* early = _cfg.get_block_for_node(spill);
    _cfg.unmap_node_from_block(spill);
    early->find_remove(spill);
    Block* lca = nullptr;
    for (DUIterator_Fast imax, i = spill->fast_outs(imax); i < imax; i++) {
      Node* out = spill->fast_out(i);
      lca = _cfg.raise_LCA_above_use(lca, out, spill);
    }
    assert(early->dominates(lca), "");
    Block* min_lca = lca;
    if (lca != early) {
      double min_freq = lca->_freq;
      while (true) {
        lca = lca->_idom;
        if (lca->_freq < min_freq) {
          min_lca = lca;
          min_freq = lca->_freq;
        }
        if (lca == early) {
          break;
        }
      }
    }

    uint insert_idx;
    Node* spilt = spill->in(1);
    if (_cfg.get_block_for_node(spilt) == min_lca) {
      insert_idx = min_lca->find_node(spilt) + 1;
      while (min_lca->get_node(insert_idx)->is_Proj()) {
        insert_idx++;
      }
    } else {
      insert_idx = 1;
      while (true) {
        Node* n = min_lca->get_node(insert_idx);
        if (n->is_Proj() || n->is_Phi() ||
            (n->is_Mach() && n->as_Mach()->ideal_Opcode() == Op_CreateEx)) {
          insert_idx++;
          continue;
        }
        break;
      }
    }
    min_lca->insert_node(spill, insert_idx);
    _cfg.map_node_to_block(spill, min_lca);
  }
  DEBUG_ONLY(_cfg.verify());
}

static void collect_uses(const PhaseCFG& cfg, GrowableArray<Pair<Node*, uint>>& uses, Node* def, Node* exclusion) {
  uint phi_input = 0;
  for (DUIterator_Fast imax, i = def->fast_outs(imax); i < imax;) {
    Node* out = def->fast_out(i);
    if (out == exclusion) {
      i++;
      continue;
    }

    bool req = false;
    bool needs_reg = false;
    uint reg_limit = out->req();
    JVMState* jvms = out->jvms();
    if (jvms != nullptr) {
      reg_limit = jvms->debug_start();
    }
    for (phi_input++; phi_input < out->req(); phi_input++) {
      if (out->in(phi_input) == def) {
        req = true;
        if (phi_input < reg_limit) {
          needs_reg = true;
        }
        break;
      }
    }
    if (!req) {
      phi_input = 0;
      i++;
      continue;
    }
    if (!out->is_Phi()) {
      phi_input = 0;
      i++;
    }

    assert(!out->is_Phi() || needs_reg, "");
    // Insertion sort
    int insert_idx;
    Block& out_block = *cfg.get_block_for_node(out);
    int out_idx = out_block.find_node(out);
    for (insert_idx = 0; insert_idx < uses.length(); insert_idx++) {
      Node* other = uses.at(insert_idx).first;
      Block& other_block = *cfg.get_block_for_node(other);
      if (out_block._rpo > other_block._rpo) {
        continue;
      } else if (out_block._rpo < other_block._rpo) {
        break;
      }
      int other_idx = other_block.find_node(other);
      if (out_idx < other_idx) {
        break;
      }
    }
    uses.insert_before(insert_idx, {out, phi_input + (needs_reg ? 0 : -1)});
  }
}

static Block& find_reload_block(const PhaseCFG& cfg, Block& def_block,
                                Block& out_block, Block& hrp_block) {
  Block* reload_block = &out_block;
  Block* min_block = reload_block;
  double min_freq = min_block->_freq;
  while (true) {
    // Hoist the reload outside of loops until the outer loop contains the
    // hrp_block itself
    CFGLoop* loop = reload_block->_loop;
    if (loop->in_loop_nest(&hrp_block)) {
      break;
    }
    Block* head = loop->head();
    Block* new_reload_block = cfg.get_block_for_node(head->pred(LoopNode::EntryControl));
    if (!def_block.dominates(new_reload_block)) {
      break;
    }
    reload_block = new_reload_block;
    if (reload_block->_freq < min_freq) {
      min_block = reload_block;
      min_freq = min_block->_freq;
    }
  }
  assert(min_block->dominates(&out_block), "");
  return *min_block;
}

void PhaseSpill::spill(Node* spilt, Block& hrp_block, uint hrp_idx) {
  ResourceMark rm;
  Block* def_block = _cfg.get_block_for_node(spilt);
  Node* reg_to_mem = _spill_map.at(spilt->_idx);
  if (reg_to_mem == nullptr) {
    int ireg = spilt->ideal_reg();
    reg_to_mem = new MachSpillCopyNode(MachSpillCopyNode::SpillRegToMem, spilt,
                                       *Matcher::idealreg2regmask[ireg],
                                       *C->matcher()->idealreg2spillmask[ireg]);
    _spill_map.at(spilt->_idx) = reg_to_mem;
    _spill_list.append(reg_to_mem);
    Node* def_end = def_block->end();
    int insert_idx;
    if (def_end->is_Catch() && def_end->in(0)->in(0) == spilt->in(0)) {
      // This is an output of a function call that can throw, it is not
      // actually available here, def_block is the fallthrough successor
      // instead
      CatchProjNode* catch_proj = def_block->get_node(def_block->end_idx() + 1)->as_CatchProj();
      if (catch_proj->_con == CatchProjNode::fall_through_index) {
        def_block = def_block->_succs[0];
      } else {
        def_block = def_block->_succs[1];
      }
      insert_idx = 1;
      while (true) {
        Node* n = def_block->get_node(insert_idx);
        if (!(n->is_Proj() || (n->is_Mach() && n->as_Mach()->ideal_Opcode() == Op_CreateEx))) {
          break;
        }
        insert_idx++;
      }
    } else {
      insert_idx = def_block->find_node(spilt) + 1;
      while (true) {
        if (!def_block->get_node(insert_idx)->is_Proj()) {
          break;
        }
        insert_idx++;
      }
    }

    def_block->insert_node(reg_to_mem, insert_idx);
    _cfg.map_node_to_block(reg_to_mem, def_block);
  }
  hrp_block.end()->add_prec(reg_to_mem);

  GrowableArray<Pair<Node*, uint>> uses;
  collect_uses(_cfg, uses, spilt, reg_to_mem);

  assert(def_block->dominates(&hrp_block), "");
  SpillStatus analysis(_cfg, _blocks, spilt, reg_to_mem, *def_block, hrp_block, hrp_idx);
  for (int use_idx = 0; use_idx < uses.length(); use_idx++) {
    Node* out = uses.at(use_idx).first;
    Block& out_block = out->is_Phi() ? *_cfg.get_block_for_node(out->in(0)->in(uses.at(use_idx).second))
                                     : *_cfg.get_block_for_node(out);
    SpillStatus::Status out_status = analysis.status(out_block, out);
    assert(out_status != SpillStatus::Status::undefined, "");
    if (out_status != SpillStatus::Status::on_stack || uses.at(use_idx).second == uint(-1)) {
      continue;
    }
    Block& reload_block = find_reload_block(_cfg, *def_block, out_block, hrp_block);
    analysis.reload(reload_block, out);
  }
  analysis.optimize();

  GrowableArray<Node*> reloads;
  auto create_reload = [&]() {
    Node* res = new MachSpillCopyNode(MachSpillCopyNode::SpillMemToReg, reg_to_mem,
                                      reg_to_mem->out_RegMask(), reg_to_mem->in_RegMask(1));
    return res;
  };
  auto register_node = [&](Block& block, Node* n) {
    _spill_map.at_put_grow(n->_idx, reg_to_mem);
    _reload_list.append(n);
    reloads.append(n);
    block.add_inst(n);
    _cfg.map_node_to_block(n, &block);
  };

  for (int use_idx = 0; use_idx < uses.length(); use_idx++) {
    Node* out = uses.at(use_idx).first;
    uint phi_input = uses.at(use_idx).second;
    Block& out_block = out->is_Phi() ? *_cfg.get_block_for_node(out->in(0)->in(phi_input))
                                     : *_cfg.get_block_for_node(out);
    SpillStatus::Status out_status = analysis.status(out_block, out);
    Node* new_def;
    if (out_status == SpillStatus::Status::on_stack) {
      assert(phi_input == uint(-1), "");
      new_def = reg_to_mem;
    } else {
      assert(out_status == SpillStatus::Status::in_register ||
             out_status == SpillStatus::Status::reloading, "");
      new_def = analysis.materialize(out_block, out, create_reload, register_node);
    }
    if (out->is_Phi()) {
      out->set_req(phi_input, new_def);
    } else {
      for (uint i = 0; i < out->req(); i++) {
        if (out->in(i) == spilt) {
          out->set_req(i, new_def);
        }
      }
    }
  }

  for (Node* reload : reloads) {
    Block& block = *_cfg.get_block_for_node(reload);
    block.find_remove(reload);
    if (reload->is_Phi()) {
      block.insert_node(reload, 1);
      continue;
    }
    uint idx = block.end_idx();
    for (DUIterator_Fast imax, i = reload->fast_outs(imax); i < imax; i++) {
      Node* out = reload->fast_out(i);
      if (_cfg.get_block_for_node(out) != &block) {
        continue;
      }
      idx = MIN2(idx, block.find_node(out));
    }
    block.insert_node(reload, idx);
  }
}

PhaseSpill::BlockInfo::BlockInfo(Arena& arena)
  : _livein(&arena, 0, 0, {}), _liveout(&arena, 0, 0, {}) {}

void PhaseSpill::BlockInfo::compute_max_pressure(const RegPressure& limit,
                                                 GrowableArray<Node*>& temp) {
  RegPressure curr;
  GrowableArray<Node*>& killed = temp;
  killed.clear();
  for (int i = 0; i < _liveout.length(); i++) {
    Node* n = _liveout.at(i).node;
    assert(!killed.contains(n), "");
    killed.append(n);
    curr = curr.add(RegPressure(n));
  }

  uint bound = find_first_node(*_block);
  for (uint node_idx = _block->number_of_nodes() - 1; node_idx >= bound; node_idx--) {
    auto consume_input = [&](Node* in) {
      if (in == nullptr || RegPressure(in).empty()) {
        return RegPressure();
      }
      if (killed.contains(in)) {
        return RegPressure();
      }

      killed.append(in);
      return RegPressure(in);
    };

    Node* n = _block->get_node(node_idx);
    curr = curr.sub(RegPressure(n));
    if (node_idx > bound) {
      curr = curr.add(consume_input(_block->get_node(node_idx - 1)));
    }
    for (uint i = 1; i < n->req(); i++) {
      curr = curr.add(consume_input(n->in(i)));
    }
    _hrp.update(node_idx, curr, limit);
  }
}

SpillStatus::SpillStatus(PhaseCFG& cfg, const GrowableArrayView<Block*>& blocks,
                         Node* spilt, Node* stack, Block& def_block, Block& hrp_block, uint hrp_idx)
  : _cfg(cfg), _blocks(blocks), _data(blocks.length() + 1, blocks.length() + 1, VirtualNode()),
    _spilt(spilt), _stack(stack), _def_block(def_block), _hrp_block(hrp_block), _hrp_idx(hrp_idx) {
  for (int i = 0; i < blocks.length(); i++) {
    if (def_block.dominates(blocks.at(i))) {
      _data.at(i)._status = Status::in_register;
      _data.at(i)._vir_idx = -1;
    }
  }
  _data.at(hrp_entry_idx())._status = Status::in_register;
  _data.at(hrp_entry_idx())._vir_idx = -1;
  _data.at(hrp_block._rpo)._status = Status::on_stack;
  _data.at(hrp_block._rpo)._vir_idx = -2;
  update(false);
}

int SpillStatus::vir_idx(const Block& block, Node* use) const {
  if (&block == &_hrp_block && !use->is_Phi() && _cfg.get_block_for_node(use) == &block) {
    uint use_idx = block.find_node(use);
    if (use_idx < _hrp_idx) {
      return _data.length() - 1;
    }
  }
  return block._rpo;
}

SpillStatus::Status SpillStatus::status(const Block& block, Node* use) const {
  return _data.at(vir_idx(block, use))._status;
}

void SpillStatus::reload(const Block& block, Node* use) {
  int vir_idx = this->vir_idx(block, use);
  VirtualNode& vir_node = _data.at(vir_idx);
  assert(vir_node._status == Status::on_stack, "");
  vir_node._status = Status::reloading;
  vir_node._vir_idx = vir_idx;
  update(false);
}

template <class F1, class F2>
Node* SpillStatus::materialize(Block& block, Node* use, F1 create_reload, F2 register_node) {
  int vir_idx = this->vir_idx(block, use);
  VirtualNode& vir_node = _data.at(vir_idx);
  assert(vir_node._status == Status::in_register || vir_node._status == Status::reloading, "");
  if (vir_node._node != nullptr) {
    return vir_node._node;
  }
  if (vir_node._status == Status::reloading) {
    Node* res = create_reload();
    vir_node._node = res;
    register_node(block, res);
    return res;
  }
  int referred_idx = vir_node._vir_idx;
  if (referred_idx != vir_idx) {
    return referred_idx == -1 ? _spilt
                              : materialize(*_blocks.at(referred_idx), use, create_reload, register_node);
  }

  Node* res = new PhiNode(block.head(), _spilt->bottom_type());
  vir_node._node = res;
  register_node(block, res);
  for (uint pred_idx = 1; pred_idx < block.num_preds(); pred_idx++) {
    Block& pred = *_cfg.get_block_for_node(block.pred(pred_idx));
    Node* in;
    if (_data.at(pred._rpo)._status == Status::on_stack) {
      in = create_reload();
      register_node(pred, in);
    } else {
      in = materialize(pred, res, create_reload, register_node);
    }
    res->init_req(pred_idx, in);
  }
  return res;
}

void SpillStatus::update(bool optimize) {
  ResourceMark rm;
  GrowableArray<Block*> worklist;

  for (int i = _blocks.length() - 1; i >= 0; i--) {
    if (_blocks.at(i) == &_hrp_block || _blocks.at(i) == &_def_block) {
      continue;
    }
    if (optimize) {
      if (_data.at(i)._status == Status::reloading) {
        worklist.append(_blocks.at(i));
      }
    } else {
      VirtualNode& vir_node = _data.at(i);
      if (vir_node._status != Status::reloading && vir_node._status != Status::undefined) {
        vir_node._status = Status::unspecified;
        worklist.append(_blocks.at(i));
      }
    }
  }

  while (worklist.is_nonempty()) {
    Block& curr = *worklist.at(worklist.length() - 1);
    worklist.remove_at(worklist.length() - 1);
    if (&curr == &_hrp_block) {
      continue;
    }

    bool changed = _data.at(curr._rpo).update(_cfg, _data, curr, curr._rpo, optimize);
    if (changed) {
      for (uint i = 0; i < curr._num_succs; i++) {
        worklist.append_if_missing(curr._succs[i]);
      }
    }
  }

  _data.at(hrp_entry_idx()).update(_cfg, _data, _hrp_block, hrp_entry_idx(), optimize);
}

void SpillStatus::optimize() {
  update(true);
}

bool SpillStatus::VirtualNode::update(const PhaseCFG& cfg, const GrowableArrayView<VirtualNode>& data,
                                      Block& block, int idx, bool optimize_reloads) {
  assert(_node == nullptr, "");
  constexpr double uncommon_threshold = 0.1;
  if (_status == Status::undefined ||
      (!optimize_reloads && _status == Status::reloading)) {
    return false;
  }

  Status curr_status;
  int curr_vir;
  if (&block == block._loop->head()) {
    Block& entry = *cfg.get_block_for_node(block.pred(LoopNode::EntryControl));
    Block& loopback = *cfg.get_block_for_node(block.pred(LoopNode::LoopBackControl));
    const VirtualNode& entry_vir_node = data.at(entry._rpo);
    const VirtualNode& loopback_vir_node = data.at(loopback._rpo);
    if (entry_vir_node._status == Status::undefined ||
        entry_vir_node._status == Status::unspecified) {
      return false;
    }
    assert(loopback_vir_node._status != Status::undefined, "");
    if (loopback_vir_node._status == Status::unspecified) {
      curr_status = entry_vir_node._status == Status::on_stack ? Status::on_stack
                                                               : Status::in_register;
      curr_vir = entry_vir_node._vir_idx;
    } else {
      curr_status = loopback_vir_node._status == Status::on_stack ? Status::on_stack
                                                                  : Status::in_register;
      curr_vir = loopback_vir_node._vir_idx;
      if (entry_vir_node._status == Status::in_register && curr_vir == idx) {
        // x = phi(e, x) -> x = e
        curr_vir = entry_vir_node._vir_idx;
      } else if (curr_status == Status::in_register && entry_vir_node._vir_idx != curr_vir) {
        curr_vir = idx;
      }
    }
  } else {
    double in_register_freq = 0;
    double total_freq = 0;
    Block& first_pred = *cfg.get_block_for_node(block.pred(1));
    curr_vir = data.at(first_pred._rpo)._vir_idx;
    for (uint pred_idx = 1; pred_idx < block.num_preds(); pred_idx++) {
      Block& pred = *cfg.get_block_for_node(block.pred(pred_idx));
      const VirtualNode& pred_vir_node = data.at(pred._rpo);
      if (pred_vir_node._status == Status::undefined ||
          pred_vir_node._status == Status::unspecified) {
        return false;
      }

      total_freq += pred._freq;
      if (pred_vir_node._status != Status::on_stack) {
        in_register_freq += pred._freq;
      }
      if (curr_vir != pred_vir_node._vir_idx) {
        curr_vir = -2;
      }
    }
    curr_status = in_register_freq < total_freq * uncommon_threshold
                  ? Status::on_stack : Status::in_register;
    if (curr_status == Status::in_register && curr_vir == -2) {
      // This is a phi combining different nodes
      curr_vir = idx;
    }
  }

  assert(curr_status != Status::on_stack || curr_vir == -2, "");
  if (curr_status == Status::on_stack && _status == Status::reloading) {
    return false;
  }
  if (_status == curr_status && _vir_idx == curr_vir) {
    return false;
  }
  _status = curr_status;
  _vir_idx = curr_vir;
  return true;
}

RegPressure::RegPressure(int int_pressure, int float_pressure, int mask_pressure)
  : _int(int_pressure), _float(float_pressure), _mask(mask_pressure) {
  assert(_int >= 0 && _float >= 0 && _mask >= 0, "");
}

RegPressure::RegPressure(const Node* n) : _int(0), _float(0), _mask(0) {
  const auto& reg_mask = n->out_RegMask();
  if (n->ideal_reg() == MachProjNode::fat_proj) {
    RegMask int_reg = reg_mask;
    int_reg.AND(*Matcher::idealreg2regmask[Op_RegI]);
    _int = int_reg.Size();
    RegMask float_reg = reg_mask;
    float_reg.AND(*Matcher::idealreg2regmask[Op_RegF]);
    _float = float_reg.Size();
    RegMask mask_reg = reg_mask;
    mask_reg.AND(*Matcher::idealreg2regmask[Op_RegVectMask]);
    _mask = mask_reg.Size();
    return;
  }

  if (reg_mask.overlap(Matcher::STACK_ONLY_mask)) {
    return;
  }

  if (reg_mask.overlap(*Matcher::idealreg2regmask[Op_RegI])) {
    _int = 1;
  } else if (reg_mask.overlap(*Matcher::idealreg2regmask[Op_RegF])) {
    _float = 1;
  } else if (reg_mask.overlap(*Matcher::idealreg2regmask[Op_RegVectMask])) {
    _mask = 1;
  }
}

RegPressure RegPressure::add(const RegPressure& other) const {
  return RegPressure(_int + other._int, _float + other._float, _mask + other._mask);
}

RegPressure RegPressure::sub(const RegPressure& other) const {
  assert(_int >= other._int && _float >= other._float && _mask >= other._mask, "");
  return RegPressure(_int - other._int, _float - other._float, _mask - other._mask);
}

RegPressure RegPressure::componentwise_max(const RegPressure& other) const {
  return RegPressure(MAX2(_int, other._int),
                     MAX2(_float, other._float),
                     MAX2(_mask, other._mask));
}

bool RegPressure::contains(const RegPressure& other) const {
  return _int >= other._int && _float >= other._float && _mask >= other._mask;
}

bool RegPressure::relieve_by(const RegPressure& sub, const RegPressure& limit) const {
  return (_int > limit._int && sub._int > 0) ||
         (_float > limit._float && sub._float > 0) ||
         (_mask > limit._mask && sub._mask > 0);
}

RegPressure RegPressure::limit() {
  int int_pressure = Matcher::idealreg2regmask[Op_RegI]->Size();
  int float_pressure = Matcher::idealreg2regmask[Op_RegF]->Size();
  int mask_pressure = Matcher::idealreg2regmask[Op_RegVectMask]->Size();
  return RegPressure(int_pressure, float_pressure, mask_pressure);
}

void HighPressureInfo::update(int idx, const RegPressure& curr, const RegPressure& limit) {
  bool hrp = false;
  if (limit._int < curr._int) {
    hrp = true;
    _int_idx = idx;
    _int_hrp = curr;
  }
  if (limit._float < curr._float) {
    hrp = true;
    _float_idx = idx;
    _float_hrp = curr;
  }
  if (limit._mask < curr._mask) {
    hrp = true;
    _mask_idx = idx;
    _mask_hrp = curr;
  }
  if (hrp) {
    _first_idx = idx;
    _first_hrp = curr;
  }
}

#ifdef ASSERT
bool PhaseSpill::verify_live_info() const {
  ResourceMark rm;
  assert(_blocks.at(0)->head()->is_Root(), "");
  GrowableArray<DistanceDatum> temp_live;
  for (int i = 1; i < _blocks.length(); i++) {
    Block* b = _blocks.at(i);
    const auto& info = _live_info.at(b->_rpo);
    temp_live.clear();
    calculate_liveout(_cfg, temp_live, _live_info, *b);
    if (!equals(info._liveout, temp_live)) {
      return false;
    }
    temp_live.clear();
    calculate_live(temp_live, info._liveout, *b, find_first_node(*b));
    if (!equals(info._livein, temp_live)) {
      return false;
    }
  }
  return true;
}
#endif // ASSERT

#ifndef PRODUCT
void PhaseSpill::BlockInfo::dump() const {
  tty->print_cr("\nB%d:\nLivein:", _block->_pre_order);
  for (int i = 0; i < _livein.length(); i++) {
    const DistanceDatum& e = _livein.at(i);
    e.node->dump();
    tty->print_cr("Max height: %d, distance: %d", e.max_height, e.distance);
  }
  tty->cr();
  tty->print_cr("Liveout:");
  for (int i = 0; i < _liveout.length(); i++) {
    const DistanceDatum& e = _liveout.at(i);
    e.node->dump();
    tty->print_cr("Max height: %d, distance: %d", e.max_height, e.distance);
  }
}

void SpillStatus::dump() const {
  tty->print("Spill status\n# node:");
  _spilt->dump();
  tty->print_cr("# hrp_block: B%d, hrp_idx: %d", _hrp_block._pre_order, _hrp_idx);
  for (int i = 0; i < _blocks.length(); i++) {
    tty->print_cr("# B%d: idx - %d, status - %d, vir_idx - %d",
                  _blocks.at(i)->_pre_order, i, int(_data.at(i)._status), _data.at(i)._vir_idx);
  }
  tty->print_cr("# hrp_entry: idx - %d. status - %d, vir_idx - %d",
                hrp_entry_idx(), int(_data.at(hrp_entry_idx())._status),
                _data.at(hrp_entry_idx())._vir_idx);
}
#endif // PRODUCT
