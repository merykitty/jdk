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

#ifndef SHARE_OPTO_PHASELOWERING_HPP
#define SHARE_OPTO_PHASELOWERING_HPP

#include "opto/phase.hpp"

class Compile;
class PhaseIterGVN;
class Unique_Node_List;
class VectorSet;

class PhaseLowering : public Phase {
private:
  PhaseIterGVN& _igvn;
public:
  PhaseLowering(PhaseIterGVN& igvn) : Phase(Phase::Lowering), _igvn(igvn) {}
  void do_transform();
};

class LowerMacroLogic {
public:
  static void optimize_logic_cones(Compile* C, PhaseIterGVN &igvn);
};

#endif // SHARE_OPTO_PHASELOWERING_HPP