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

#ifndef SHARE_OPTO_PHASELCM_HPP
#define SHARE_OPTO_PHASELCM_HPP

#include "opto/phase.hpp"

class Block;
class Node;
class PhaseCFG;
class PhaseChaitin;
class SBlock;
class SUnit;

class PhaseLCM : public Phase {
private:
  PhaseCFG& _cfg;
  PhaseChaitin& _regalloc;
public:
  PhaseLCM(PhaseCFG& cfg, PhaseChaitin& regalloc)
    : Phase(Phase::LCM), _cfg(cfg), _regalloc(regalloc) {}
  bool schedule(Block& block);

  class NodeData {
  public:
    int idx_in_sched;
    int vertex_idx;
    SUnit* sunit;

    NodeData() : idx_in_sched(-1), vertex_idx(-1), sunit(nullptr) {}
  };
};

class SUnit : public ResourceObj {
private:
  NONCOPYABLE(SUnit);

public:
  class Pressure {
  private:
    friend class SUnit;

    int _int;
    int _float;
    int _mask;

    Pressure() : _int(0), _float(0), _mask(0) {}
    Pressure(int int_pressure, int float_pressure, int mask_pressure);

  public:
    Pressure(const Node* n);
    Pressure add(const Pressure& other) const;
    Pressure componentwise_max(const Pressure& other) const;
    bool less_than(const Pressure& other) const;
    int total_pressure() const { return _int + _float + _mask; }
  };

  class SDep : public ResourceObj {
  private:
    SUnit* _pred;
    SUnit* _succ;
    Pressure _pressure;

  public:
    SDep(SUnit* pred, SUnit* succ, const Pressure& pressure)
      : _pred(pred), _succ(succ), _pressure(pressure) {}
    void add_pressure(const Pressure& pressure) { _pressure = _pressure.add(pressure); }
    SUnit* pred() { return _pred; }
    SUnit* succ() { return _succ; }
    const Pressure& pressure() const { return _pressure; }
  };

  enum class SethiUllmanStatus {
    not_calculated,
    calculating,
    calculated
  };

private:
  const Node* _def;
  GrowableArray<Node*> _nodes;
  GrowableArray<SDep*> _preds;
  GrowableArray<SDep*> _succs;
  Pressure _temp_pressure;
  Pressure _out_pressure;
  SethiUllmanStatus _sethi_ullman;
  Pressure _sethi_ullman_value;
  int _unsched_outs;

  SUnit() : _def(nullptr), _sethi_ullman(SethiUllmanStatus::not_calculated),
            _unsched_outs(0) {}
  SUnit(Node* n, GrowableArrayView<PhaseLCM::NodeData>& node_data
#ifdef ASSERT
      , int start_idx, int end_idx
#endif // ASSERT
  );

public:
  static SUnit* try_create(Node* n, GrowableArrayView<PhaseLCM::NodeData>& node_data
#ifdef ASSERT
                         , int start_idx, int end_idx
#endif // ASSERT
  );
  static SUnit* create_sink(const SBlock& block, const GrowableArrayView<SUnit*>& units);
  static void calculate_sethi_ullman_numbers(SUnit* root);
  void add_predecessors(const SBlock& block,
                        const GrowableArrayView<PhaseLCM::NodeData>& node_data);
  void schedule(GrowableArray<SUnit*>& worklist);
  Node** expand(Node** start) const;
  GrowableArray<Node*> expand() const;

#ifdef ASSERT
  bool has_sethi_ullman() const {
    return _sethi_ullman == SethiUllmanStatus::calculated;
  }
#endif // ASSERT

#ifndef PRODUCT
  void dump();
#endif // PRODUCT
};

class SBlock {
private:
  NONCOPYABLE(SBlock);
  GrowableArrayView<Node*>& _scheduled;
  int _start_idx;
  int _end_idx;
  SUnit* _sink;
  GrowableArray<SUnit*> _units;
  const GrowableArrayView<PhaseLCM::NodeData>& _node_data;

public:
  SBlock(GrowableArrayView<Node*>& scheduled, int start_idx, int end_idx,
         GrowableArrayView<PhaseLCM::NodeData>& node_data);
  bool contains(const Node* n) const;
  template <class F>
  bool schedule(F random);

#ifndef PRODUCT
  void dump();
#endif // PRODUCT
};

#endif // SHARE_OPTO_PHASELCM_HPP
