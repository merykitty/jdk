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

#ifndef SHARE_OPTO_PHASESPILL_HPP
#define SHARE_OPTO_PHASESPILL_HPP

#include "opto/phase.hpp"
#include "utilities/growableArray.hpp"

class RegPressure {
private:
  friend class HighPressureInfo;
  int _int;
  int _float;
  int _mask;

  RegPressure(int int_pressure, int float_pressure, int mask_pressure);

public:
  RegPressure() : RegPressure(0, 0, 0) {}
  RegPressure(const Node* n);
  RegPressure add(const RegPressure& other) const;
  RegPressure sub(const RegPressure& other) const;
  RegPressure componentwise_max(const RegPressure& other) const;
  bool contains(const RegPressure& other) const;
  bool empty() const { return _int == 0 && _float == 0 && _mask == 0; }
  bool relieve_by(const RegPressure& sub, const RegPressure& limit) const;

  static RegPressure limit();
};

class HighPressureInfo {
private:
  int _int_idx;
  RegPressure _int_hrp;
  int _float_idx;
  RegPressure _float_hrp;
  int _mask_idx;
  RegPressure _mask_hrp;
  int _first_idx;
  RegPressure _first_hrp;

public:
  HighPressureInfo() : _int_idx(-1), _float_idx(-1), _mask_idx(-1), _first_idx(-1) {}
  void update(int idx, const RegPressure& curr, const RegPressure& limit);
  int first_idx() const { return _first_idx; }
  const RegPressure& first_hrp() const { return _first_hrp; }
};

// A more generalized PhaseLive, estimates the number of instructions from
// block boundaries to the nearest use of a node, infinity means the node is
// dead.
class PhaseSpill : public Phase {
public:
  class DistanceDatum {
  public:
    Node* node;
    int distance;
    // The max loop height of all blocks between the current block and next use
    int max_height;
  };

  class BlockInfo {
  private:
    friend class PhaseSpill;
    const Block* _block;
    GrowableArray<DistanceDatum> _livein;
    GrowableArray<DistanceDatum> _liveout;
    HighPressureInfo _hrp;

  public:
    BlockInfo() { ShouldNotCallThis(); }
    BlockInfo(Arena& arena);
    const GrowableArrayView<DistanceDatum>& livein() const { return _livein; }
    void compute_max_pressure(const RegPressure& limit, GrowableArray<Node*>& temp);
#ifndef PRODUCT
    void dump() const;
#endif // PRODUCT
  };

private:
  PhaseCFG& _cfg;
  Arena _arena;
  GrowableArray<Block*> _blocks;
  GrowableArray<BlockInfo> _live_info;
  RegPressure _limit_pressure;
  GrowableArray<Node*> _spill_map;
  GrowableArray<Node*> _spill_list;
  GrowableArray<Node*> _reload_list;

  bool should_spill() const { return !C->has_irreducible_loop(); }
  void compute_live();
  void spill(Node* spilt, Block& hrp, uint hrp_idx);
#ifdef ASSERT
  bool verify_live_info() const;
#endif

public:
  PhaseSpill(PhaseCFG& cfg);
  void do_spilling();
};

class SpillStatus {
public:
  enum class Status {
    undefined,
    unspecified, // The status has not been computed yet
    in_register,
    on_stack,
    reloading
  };

  class VirtualNode {
  private:
    friend class SpillStatus;
    Status _status;
    int _vir_idx;
    Node* _node;
  
  public:
    VirtualNode() : _status(Status::undefined), _vir_idx(-2), _node(nullptr) {}
    bool update(const PhaseCFG& cfg, const GrowableArrayView<VirtualNode>& data,
                Block& block, int idx, bool optimize_reloads);
  };

private:
  PhaseCFG& _cfg;
  const GrowableArrayView<Block*>& _blocks;
  GrowableArray<VirtualNode> _data;
  Node* _spilt;
  Node* _stack;
  Block& _def_block;
  Block& _hrp_block;
  uint _hrp_idx;

  int vir_idx(const Block& block, Node* use) const;
  int hrp_entry_idx() const { return _data.length() - 1; }
  void update(bool optimize);

public:
  SpillStatus(PhaseCFG& cfg, const GrowableArrayView<Block*>& blocks,
              Node* spilt, Node* stack, Block& def_block, Block& hrp_block, uint hrp_idx);
  Status status(const Block& block, Node* use) const;
  void reload(const Block& block, Node* use);
  void optimize();

  template <class F1, class F2>
  Node* materialize(Block& block, Node* use, F1 create_reload, F2 register_node);

#ifndef PRODUCT
  void dump() const;
#endif // PRODUCT
};

#endif // SHARE_OPTO_PHASESPILL_HPP
