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
#include "opto/ad.hpp"
#include "opto/chaitin.hpp"
#include "opto/phaselcm.hpp"

// An independent node can be scheduled independently
static bool is_independent(const Node* n) {
  if (n->is_Start() || n->is_Region() || n->is_Catch()) {
    return true;
  }
  // IfTrue, IfFalse, Phi, etc must all be scheduled right after
  // their predecessors
  if (!n->is_Mach()) {
    return false;
  }
  // MachTemps must be scheduled right before their successors
  // MachProjs must be scheduled right after their predecessors
  // MachNullChecks must be scheduled right after their predecessors
  if (n->is_MachTemp() || n->is_MachProj() || n->is_MachNullCheck()) {
    return false;
  }

  return true;
}

SUnit::SUnit(const PhaseCFG& cfg, GrowableArray<SUnit*>& node_map, Node* n)
  : _is_first(false), _is_prioritized(false), _is_last(false),
    _is_call(false), _is_out(false) {
  Block* block = cfg.get_block_for_node(n);
  auto add_node = [&](const Node* n) {
    assert(cfg.get_block_for_node(n) == block, "must belong to the same Block");
    _nodes.append(n);
    assert(node_map.length() <= n->_idx || node_map.at(n->_idx) == nullptr,
           "A Node can only belong to 1 SUnit");
    node_map.at_put_grow(n->_idx, this);
  };

  for (size_t i = 0; i < n->req(); i++) {
    Node* in = n->in(i);
    if (in != nullptr && in->is_MachTemp()) {
      _temp_pressure = _temp_pressure.add(Pressure(in));
      add_node(in);
    }
  }

  add_node(n);

  Node_List worklist;
  while (worklist.size() > 0) {
    Node* parent = worklist.pop();
    for (DUIterator_Fast imax, i = parent->fast_outs(imax); i < imax; i++) {
      Node* out = parent->fast_out(i);
      if (is_independent(out)) {
        continue;
      }

      add_node(out);
      worklist.push(out);
      // These must come at the end of the block
      if (out->is_IfTrue()) {
        _is_last = true;
      }
    }
  }

  if (n->is_Mach() && n->as_Mach()->has_call()) {
    _is_call = true;
  }

  // These must come at the start of the block
  if (n->is_Start() || n->is_Region()) {
    assert(!_is_last, "sanity");
    _is_first = true;
    return;
  }

  // These must come at the end of the block
  if (n->is_Catch() || n->as_Mach()->ideal_Opcode() == Op_Rethrow) {
    _is_last = true;
    return;
  }

  // These must be scheduled as soon as they are ready
  if (n->as_Mach()->ideal_Opcode() == Op_CreateEx) {
    assert(!_is_last, "sanity");
    _is_prioritized = true;
  }
}

SUnit* SUnit::try_create(const PhaseCFG& cfg, GrowableArray<SUnit*>& node_map, Node* n) {
  // It is theoretically possible to schedule flags independently but it would
  // be easier to stick them with their successors
  if (!is_independent(n) || must_clone[n->as_Mach()->ideal_Opcode()]) {
    return nullptr;
  }

  Block* block = cfg.get_block_for_node(n);
  SUnit* unit = new SUnit(cfg, node_map, n);

  // Schedule flags with their successors
  Node_List worklist;
  worklist.push(n);
  while (worklist.size() > 0) {
    Node* child = worklist.pop();
    for (size_t i = 0; i < child->req(); i++) {
      Node* in = child->in(i);
      if (in == nullptr || !in->is_Mach()) {
        continue;
      }
      if (must_clone[in->as_Mach()->ideal_Opcode()]) {
        assert(block == cfg.get_block_for_node(in),
               "flag must come with its successor");
        SUnit* pred = new SUnit(cfg, node_map, in);
        unit->_nodes.insert_before(0, &pred->_nodes);
        for (const Node* pred_node : pred->_nodes) {
          node_map.at(pred_node->_idx) = unit;
        }
        unit->_temp_pressure = unit->_temp_pressure.max(pred->_temp_pressure);
        worklist.push(in);
      }
    }
  }

  for (const Node* n : unit->_nodes) {
    for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
      const Node* out = n->fast_out(i);
      if (cfg.get_block_for_node(out) != block) {
        unit->_is_out = true;
      }
      if (out->_idx >= node_map.length() || node_map.at(out->_idx) != unit) {
        unit->_out_pressure = unit->_out_pressure.add(Pressure(out));
      }
    }
  }

  return unit;
}

void SUnit::add_predecessors(const GrowableArray<SUnit*>& node_map) {
  for (const Node* n : _nodes) {
    for (size_t i = 0; i < n->req(); i++) {
      Node* in = n->in(i);
      if (in == nullptr || in->_idx >= node_map.length()) {
        continue;
      }

      if (Pressure(in).empty()) {
        continue;
      }

      SUnit* in_unit = node_map.at(in->_idx);
      if (in_unit == nullptr) {
        continue;
      }

      if (!_reqs.contains(in_unit)) {
        _reqs.append(in_unit);
        in_unit->_outs.append(this);
      }
    }
  }

  for (const Node* n : _nodes) {
    for (size_t i = 0; i < n->len(); i++) {
      Node* in = n->in(i);
      if (in == nullptr || in->_idx >= node_map.length()) {
        continue;
      }

      SUnit* in_unit = node_map.at(in->_idx);
      if (in_unit == nullptr) {
        continue;
      }

      if (!_reqs.contains(in_unit) && !_preds.contains(in_unit)) {
        _preds.append(in_unit);
        in_unit->_outs.append(this);
      }
    }
  }
}

SUnit::Pressure::Pressure(int int_pressure, int float_pressure, int mask_pressure)
  : _int(int_pressure), _float(float_pressure), _mask(mask_pressure) {}

SUnit::Pressure::Pressure(const Node* n) : _int(0), _float(0), _mask(0) {
  auto& reg_mask = n->out_RegMask();
  if (reg_mask.overlap(*Matcher::idealreg2regmask[Op_RegI])) {
    _int = 1;
  } else if (reg_mask.overlap(*Matcher::idealreg2regmask[Op_RegF])) {
    _float = 1;
  } else if (reg_mask.overlap(*Matcher::idealreg2regmask[Op_RegVectMask])) {
    _mask = 1;
  }
}

SUnit::Pressure SUnit::Pressure::add(const SUnit::Pressure& other) const {
  return SUnit::Pressure(_int + other._int, _float + other._float, _mask + other._mask);
}

SUnit::Pressure SUnit::Pressure::max(const SUnit::Pressure& other) const {
  return SUnit::Pressure(MAX2(_int, other._int), MAX2(_float, other._float),
                         MAX2(_mask, other._mask));
}

SBlock::SBlock(const PhaseCFG& cfg, GrowableArray<SUnit*>& node_map, const Block& block)
  : _block(block), _node_map(node_map),
    _first_unit(nullptr), _last_unit(nullptr) {
  for (size_t i = 0; i < block.number_of_nodes(); i++) {
    Node* n = block.get_node(i);
    SUnit* unit = SUnit::try_create(cfg, node_map, n);
    if (unit == nullptr) {
      continue;
    }

    _units.append(unit);
    if (unit->is_first()) {
      assert(_first_unit == nullptr, "cannot have more than 1");
      _first_unit = unit;
    } else if (unit->is_last()) {
      assert(_last_unit == nullptr, "cannot have more than 1");
      _last_unit = unit;
    }
    if (unit->is_out()) {
      _out_units.append(unit);
    }
  }
#ifdef ASSERT
  for (size_t i = 0; i < block.number_of_nodes(); i++) {
    Node* n = block.get_node(i);
    assert(node_map.at(n->_idx) != nullptr, "a Node must belong to a SUnit");
  }
#endif // ASSERT

  for (SUnit* unit : _units) {
    unit->add_predecessors();
  }
}
