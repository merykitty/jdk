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

#include "utilities/growableArray.hpp"

class Block;
class Node;

class SUnit {
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
    Pressure max(const Pressure& other) const;

    bool empty() const { return _int == 0 && _float == 0 && _mask == 0; }
    int int_pressure() const { return _int; }
    int float_pressure() const { return _float; }
    int mask_pressure() const { return _mask; }
  };

private:
  GrowableArray<const Node*> _nodes;
  GrowableArray<SUnit*> _reqs;
  GrowableArray<SUnit*> _preds;
  GrowableArray<SUnit*> _outs;
  bool _is_first;
  bool _is_prioritized;
  bool _is_last;
  bool _is_call;
  bool _is_out;
  Pressure _temp_pressure;
  Pressure _out_pressure;

  SUnit(const PhaseCFG& cfg, GrowableArray<SUnit*>& node_map, Node* n);

public:
  bool is_first() const { return _is_first; }
  bool is_last() const { return _is_last; }
  bool is_out() const { return _is_out; }

  static SUnit* try_create(const PhaseCFG& cfg, GrowableArray<SUnit*>& node_map, Node* n);
  void add_predecessors(const GrowableArray<SUnit*>& node_map);
};

class SBlock {
private:
  NONCOPYABLE(SBlock);

  const Block& _block;
  GrowableArray<SUnit*> _units;
  GrowableArray<SUnit*> _out_units;
  GrowableArray<SUnit*>& _node_map;
  SUnit* _first_unit; // The SUnit that needs to be scheduled first
  SUnit* _last_unit;  // The SUnit that needs to be scheduled last

public:
  SBlock(const PhaseCFG& cfg, GrowableArray<SUnit*>& node_map, const Block& block);
  void schedule_calls();
};

#endif // SHARE_OPTO_PHASELCM_HPP
