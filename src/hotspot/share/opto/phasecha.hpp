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

#ifndef SHARE_OPTO_PHASECHA_HPP
#define SHARE_OPTO_PHASECHA_HPP

#include "ci/ciInstanceKlass.hpp"
#include "opto/phase.hpp"

class PhaseIterGVN;
class Type;
class TypeInstPtr;
class TypeInterfaces;
class TypeKlassPtr;
class TypeTuple;
class Unique_Node_List;

class PhaseCHA : public Phase {
private:
  PhaseIterGVN& _igvn;

public:
  PhaseCHA(PhaseIterGVN& igvn) : Phase(Class_Hierarchy_Analysis), _igvn(igvn) {}
  void do_transform();

private:
  void optimize_node_type(Node* n);

  const Type* optimize_inst_oop_type(const TypeInstPtr* type);
  const TypeTuple* optimize_tuple_type(const TypeTuple* type);
  ciInstanceKlass* optimize_instance_klass(ciInstanceKlass* klass, const TypeInterfaces* interfaces);
  ciKlass* klassptr_type_has_no_subklass(const TypeKlassPtr* type);
  DEBUG_ONLY(void verify(const Unique_Node_List& node_list));
};

#endif // SHARE_OPTO_PHASECHA_HPP
