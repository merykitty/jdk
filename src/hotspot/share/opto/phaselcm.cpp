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
#include "opto/c2compiler.hpp"
#include "opto/chaitin.hpp"
#include "opto/phaselcm.hpp"

static bool collect_nodes(const PhaseCFG& cfg, const Block& block,
                          GrowableArray<Node*>& scheduled,
                          GrowableArray<Node*>& begin_nodes, GrowableArray<Node*>& end_nodes,
                          GrowableArrayView<PhaseLCM::NodeData>& node_data);

static bool schedule_calls(const Block& block, GrowableArrayView<Node*>& scheduled,
                           GrowableArray<int>& bounds,
                           const GrowableArrayView<Node*>& livein,
                           const GrowableArrayView<Node*>& liveout,
                           GrowableArray<PhaseLCM::NodeData>& node_data);

static void schedule_special_nodes(const PhaseCFG& cfg, const Block& block,
                                   GrowableArray<Node*>& scheduled);

static void add_call_projs(PhaseCFG& cfg, const Matcher& matcher, Block& block);

bool PhaseLCM::schedule(Block& block) {
  auto report_failure = [&]() {
    // Subsuming loads (e.g matching "CmpI (LoadI X) Y" into "cmp [X], Y") may
    // result in a flag being unable to stick to its use
    // The exhaustive list of the cases:
    // - A flag does not belong to the same block as its use, caught in
    //   collect_nodes
    // - The flag input of block.end() cannot be scheduled right before it,
    //   caught in collect_nodes
    // - A flag and its use are separated by a call, caught in schedule_calls
    // - A flag and its use belong to the same SBlock, but they cannot be
    //   scheduled as a whole, which results in a cycle in the dependency graph,
    //   caught in SBlock::schedule
    if (C->subsume_loads()) {
      C->record_failure(C2Compiler::retry_no_subsuming_loads());
    } else {
      assert(false, "must be schedulable");
      C->record_method_not_compilable("local schedule failed");
    }
  };

  for (uint i = 0; i < block.number_of_nodes(); i++) {
    Node* n = block.get_node(i);
    // A few node types require changing a required edge to a precedence edge
    // before allocation.
    if (n->is_Mach() && n->req() > TypeFunc::Parms &&
        (n->as_Mach()->ideal_Opcode() == Op_MemBarAcquire ||
         n->as_Mach()->ideal_Opcode() == Op_MemBarVolatile)) {
      // MemBarAcquire could be created without Precedent edge.
      // del_req() replaces the specified edge with the last input edge
      // and then removes the last edge. If the specified edge > number of
      // edges the last edge will be moved outside of the input edges array
      // and the edge will be lost. This is why this code should be
      // executed only when Precedent (== TypeFunc::Parms) edge is present.
      Node* x = n->in(TypeFunc::Parms);
      n->del_req(TypeFunc::Parms);
      n->add_prec(x);
    }
  }

  if (block.number_of_nodes() == 1) {
    return true;
  }

#ifndef PRODUCT
  if (_cfg.trace_opto_pipelining()) {
    tty->print_cr("# --- scheduling B%d, before: ---", block._pre_order);
    for (uint i = 0; i < block.number_of_nodes(); i++) {
      tty->print("# ");
      block.get_node(i)->dump();
    }
    tty->print_cr("#");
  }
#endif

  ResourceMark mark;

  GrowableArray<NodeData> node_data(C->unique());
  node_data.at_grow(C->unique() - 1);
  // Schedulable nodes, nodes with different priorities are scheduled later
  GrowableArray<Node*> scheduled(block.number_of_nodes());
  // Start, Region and children
  GrowableArray<Node*> begin_nodes;
  // MachNull, If, Catch, etc
  GrowableArray<Node*> end_nodes;
  bool success = collect_nodes(_cfg, block, scheduled, begin_nodes, end_nodes, node_data);
  if (!success) {
    report_failure();
    return false;
  }

  GrowableArray<Node*> livein;
  GrowableArray<Node*> liveout;
  if (!StressLCM && OptoRegScheduling) {
    auto get_live_in_out = [this](GrowableArray<Node*>& list, IndexSet* set) {
      IndexSetIterator iter(set);
      while (true) {
        uint lrg_idx = iter.next();
        if (lrg_idx == 0) {
          break;
        }
        LRG& lrg = _regalloc.lrgs(lrg_idx);
        list.append(lrg._def);
      }
    };

    PhaseLive* live = _regalloc.get_live();
    get_live_in_out(livein, live->livein(&block));
    get_live_in_out(liveout, live->live(&block));
    for (Node* n : begin_nodes) {
      livein.append(n);
    }
    for (Node* n : end_nodes) {
      for (uint i = 0; i < n->req(); i++) {
        Node* in = n->in(i);
        if (in != nullptr && !end_nodes.contains(in)) {
          liveout.append_if_missing(in);
        }
      }
    }
  }

  if (scheduled.length() > 1) {
    GrowableArray<int> bounds;
    bool success = schedule_calls(block, scheduled, bounds, livein, liveout, node_data);
    if (!success) {
      report_failure();
      return false;
    }

#ifndef PRODUCT
    if (_cfg.trace_opto_pipelining()) {
      tty->print_cr("# after scheduling calls:");
      for (int i = 0; i < scheduled.length(); i++) {
        tty->print("# ");
        scheduled.at(i)->dump();
      }
      tty->print_cr("#");
    }
#endif // PRODUCT

    for (int i = 0; i < bounds.length(); i += 2) {
      int begin = bounds.at(i);
      int end = bounds.at(i + 1);
      assert(begin <= end, "");
      if (end - begin <= 1) {
        continue;
      }

      SBlock sblock(scheduled, begin, end, node_data);

#ifndef PRODUCT
      if (_cfg.trace_opto_pipelining()) {
        tty->print_cr("# SBlock %d:", i / 2);
        sblock.dump();
      }
#endif // PRODUCT

      auto random = [this]() {
        return C->random();
      };
      bool success = sblock.schedule(random);
      if (!success) {
        report_failure();
        return false;
      }

#ifndef PRODUCT
      if (_cfg.trace_opto_pipelining()) {
        tty->print_cr("# after SBlock %d:", i / 2);
        for (int i = 0; i < scheduled.length(); i++) {
          tty->print("# ");
          scheduled.at(i)->dump();
        }
        tty->print_cr("#");
      }
#endif // PRODUCT
    }
  }

  // Schedule the remaining nodes
  scheduled.insert_before(0, &begin_nodes);
  scheduled.appendAll(&end_nodes);
  assert(checked_cast<int>(block.number_of_nodes()) == scheduled.length(), "");

  // Schedule CreateEx and CheckCastPP as early as possible
  schedule_special_nodes(_cfg, block, scheduled);

  assert(checked_cast<int>(block.number_of_nodes()) == scheduled.length(), "");
  // Cannot go all the way to scheduled.length() since we need to preserve the
  // order of IfTrue and IfFalse
  for (uint i = 0; i < block.end_idx(); i++) {
    block.map_node(scheduled.at(i), i);
  }

  // Signify the registers that are killed by the calls according to the calling
  // convention
  add_call_projs(_cfg, _regalloc._matcher, block);

#ifndef PRODUCT
  if (_cfg.trace_opto_pipelining()) {
    tty->print_cr("# after scheduling");
    for (uint i = 0; i < block.number_of_nodes(); i++) {
      tty->print("# ");
      block.get_node(i)->dump();
    }
    tty->print_cr("#");
  }
#endif

  return true;
}

static bool collect_nodes(const PhaseCFG& cfg, const Block& block,
                          GrowableArray<Node*>& scheduled,
                          GrowableArray<Node*>& begin_nodes, GrowableArray<Node*>& end_nodes,
                          GrowableArrayView<PhaseLCM::NodeData>& node_data) {
  // Check if there is a flag that does not belong to the same block as its use
  for (uint idx = 0; idx < block.number_of_nodes(); idx++) {
    Node* n = block.get_node(idx);
    // If a flag input is in another block
    for (uint i = 0; i < n->req(); i++) {
      Node* in = n->in(i);
      if (in == nullptr || !in->is_Mach() || !must_clone[in->as_Mach()->ideal_Opcode()]) {
        continue;
      }
      if (cfg.get_block_for_node(in) != &block) {
        return false;
      }
    }

    // If an output of a flag is in another block
    if (!n->is_Mach() || !must_clone[n->as_Mach()->ideal_Opcode()]) {
      continue;
    }
    for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
      Node* out = n->fast_out(i);
      if (cfg.get_block_for_node(out) == &block) {
        continue;
      }
      for (uint i = 0; i < out->req(); i++) {
        if (out->in(i) == n) {
          return false;
        }
      }
    }
  }

  for (uint idx = 0; idx < block.number_of_nodes(); idx++) {
    scheduled.append(block.get_node(idx));
  }

  // Begin nodes
  // The head goes first, then the head Projs, then the Phis
  Node* head = block.head();
  begin_nodes.append(head);
  scheduled.remove(head);
  for (int idx = scheduled.length() - 1; idx >= 0; idx--) {
    Node* n = scheduled.at(idx);
    if (n->is_Proj() && n->in(0) == head) {
      begin_nodes.append(n);
      scheduled.remove_at(idx);
    }
  }
  for (int idx = scheduled.length() - 1; idx >= 0; idx--) {
    Node* n = scheduled.at(idx);
    if (n->is_Phi()) {
      assert(n->in(0) == head, "");
      begin_nodes.append(n);
      scheduled.remove_at(idx);
    }
  }
  // Append naked Con to begin_nodes to reduce the number of nodes in scheduled
  for (int idx = scheduled.length() - 1; idx >= 0; idx--) {
    Node* n = scheduled.at(idx);
    int op = n->Opcode();
    if (op == Op_Con || op == Op_ConI || op == Op_ConL || op == Op_ConF ||
        op == Op_ConD || op == Op_ConP || op == Op_ConN || op == Op_ConNKlass) {
      begin_nodes.append(n);
      scheduled.remove_at(idx);
    }
  }

  for (int idx = 0; idx < scheduled.length(); idx++) {
    node_data.at(scheduled.at(idx)->_idx).idx_in_sched = idx;
  }

  Node* end = block.end();
  if (end->is_MachNullCheck()) {
    Node* mem = end->in(1);
    SUnit* end_unit = SUnit::try_create(mem, node_data
                                        DEBUG_ONLY(COMMA 0 COMMA scheduled.length()));
    end_nodes = end_unit->expand();
    end_nodes.append(end);
    for (DUIterator_Fast imax, i = end->fast_outs(imax); i < imax; i++) {
      Node* out = end->fast_out(i);
      assert(out->is_IfTrue() || out->is_IfFalse(), "");
      end_nodes.append(out);
    }
  } else {
    SUnit* end_unit = SUnit::try_create(end, node_data
                                        DEBUG_ONLY(COMMA -1 COMMA scheduled.length()));
    end_nodes = end_unit->expand();
  }
  for (Node* end : end_nodes) {
    scheduled.remove(end);
  }

  for (int idx = 0; idx < scheduled.length(); idx++) {
    Node* n = scheduled.at(idx);
    node_data.at(n->_idx).idx_in_sched = idx;
  }
  for (int idx = 0; idx < end_nodes.length(); idx++) {
    Node* n = end_nodes.at(idx);
    node_data.at(n->_idx).idx_in_sched = -1;
  }

  // Check if a node in end_nodes is the predecessor of a node in scheduled
  for (Node* end : end_nodes) {
    for (DUIterator_Fast imax, i = end->fast_outs(imax); i < imax; i++) {
      Node* out = end->fast_out(i);
      if (node_data.at(out->_idx).idx_in_sched >= 0) {
        return false;
      }
    }
  }
  return true;
}

// Schedule CreateEx and CheckCastPP as early as possible
static void schedule_special_nodes(const PhaseCFG& cfg, const Block& block,
                                   GrowableArray<Node*>& scheduled) {
  GrowableArray<Node*> special_nodes;
  for (int i = scheduled.length() - 1; i >= 0; i--) {
    Node* n = scheduled.at(i);
    if (!n->is_Mach()) {
      continue;
    }
    int iop = n->as_Mach()->ideal_Opcode();
    if (iop == Op_CreateEx || iop == Op_CheckCastPP) {
      special_nodes.append(n);
      scheduled.remove_at(i);
#ifdef ASSERT
      assert(n->req() == 2, "CreateEx and CheckCastPP can only have 1 input");
      for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
        Node* out = n->fast_out(i);
        assert(!out->is_Proj(), "CreateEx and CheckCastPP cannot have Proj output");
      }
#endif // ASSERT
    }
  }

  int begin_idx;
  for (begin_idx = 1; begin_idx < scheduled.length(); begin_idx++) {
    Node* n = scheduled.at(begin_idx);
    if (!n->is_Proj() && !n->is_Phi()) {
      break;
    }
    assert(n->in(0) == scheduled.at(0), "");
  }

  while (!special_nodes.is_empty()) {
    for (int idx = special_nodes.length() - 1; idx >= 0; idx--) {
      int pos = begin_idx - 1;
      bool delay = false;
      Node* n = special_nodes.at(idx);
      for (uint i = 0; i < n->len(); i++) {
        Node* in = n->in(i);
        if (in == nullptr) {
          continue;
        }

        int curr_pos;
        if (cfg.get_block_for_node(in) != &block) {
          curr_pos = -1;
        } else {
          curr_pos = scheduled.find(in);
          if (curr_pos == -1) {
            delay = true;
            break;
          }
        }
        pos = MAX2(pos, curr_pos);
      }
      if (delay) {
        continue;
      }

      while (true) {
        pos++;
        if (pos == scheduled.length()) {
          break;
        }
        Node* curr = scheduled.at(pos);
        if (curr->is_Proj()) {
          continue;
        }
        // CreateEx nodes have higher priorities than CheckCastPP ones
        if (!curr->is_Mach() || curr->as_Mach()->ideal_Opcode() != Op_CreateEx) {
          break;
        }
      }
      scheduled.insert_before(pos, n);
      special_nodes.remove_at(idx);
    }
  }
}

// Schedule all nodes in the basic block starting at start_idx with respects to
// call nodes. At each iteration, choose one call that can be scheduled first
// and partition the region into nodes before the call and nodes after.
// This function assumes that nodes are correctly scheduled with respects to
// start_idx, i.e. no nodes from start_idx is a direct/indirect predecessor of
// another node before start_idx.
static bool schedule_calls_helper(GrowableArrayView<Node*>& scheduled,
                                  int start_idx, int end_idx,
                                  GrowableArray<int>& bounds,
                                  const GrowableArrayView<Node*>& livein,
                                  const GrowableArrayView<Node*>& liveout,
                                  GrowableArrayView<PhaseLCM::NodeData>& node_data,
                                  int vertex_num, GrowableArrayView<double>& graph_edges,
                                  int src_idx, int snk_idx) {
  // Find a first call in the interesting region, null if there is none
  auto find_first_call = [&]() -> Node* {
    Node* call = nullptr;
    int call_cnt = 0;
    for (int i = start_idx; i < end_idx; i++) {
      Node* n = scheduled.at(i);
      if (n->is_MachCall() || (n->is_Mach() && n->as_Mach()->has_call())) {
        call = n;
        call_cnt++;
      }
    }
    if (call_cnt <= 1) {
      return call;
    }

    // Given a call, find a previous call in the interesting region
    auto find_previous_call = [&](Node* call) -> Node* {
      Node_List worklist;
      worklist.push(call);
      while (worklist.size() > 0) {
        Node* curr = worklist.pop();
        for (uint i = 0; i < curr->len(); i++) {
          Node* in = curr->in(i);
          if (in == nullptr || node_data.at(in->_idx).idx_in_sched < start_idx) {
            continue;
          }
          if (in->is_MachCall() || (in->is_Mach() && in->as_Mach()->has_call())) {
            return in;
          }
          worklist.push(in);
        }
      }
      return nullptr;
    };

    while (true) {
      Node* previous = find_previous_call(call);
      if (previous == nullptr) {
        break;
      }
      call = previous;
    }

    return call;
  };

  auto bfs = [](GrowableArray<int>& prev, GrowableArray<double>& path_weights,
                int vertex_num, const GrowableArrayView<double>& graph_edges,
                int source, int sink, GrowableArray<int>& queue) {
    prev.clear();
    prev.at_grow(vertex_num - 1, -1);
    path_weights.clear();
    path_weights.at_grow(vertex_num - 1, 0);
    path_weights.at(source) = std::numeric_limits<double>::infinity();
    queue.clear();
    queue.append(source);
    int pos = 0;
    while (pos < queue.length()) {
      int curr = queue.at(pos);
      pos++;
      for (int i = 0; i < vertex_num; i++) {
        if (prev.at(i) >= 0) {
          continue;
        }
        double edge_weight = graph_edges.at(curr * vertex_num + i);
        assert(edge_weight >= 0, "must be");
        if (edge_weight == 0) {
          continue;
        }
        prev.at(i) = curr;
        path_weights.at(i) = MIN2(edge_weight, path_weights.at(curr));
        if (i == sink) {
          break;
        }
        queue.append(i);
      }
    }
  };

  // Problem: Since a call kills everything, we try to minimize the number of
  // nodes living through the call
  //
  // Model:
  // Each node is represented by 2 vertices, node_in and node_out, the problem
  // is modelled by a cut partitioning the graph into 2 parts. A node is
  // scheduled before the call iff the corresponding in-vertex lies in the first
  // (source) partition, and a node is scheduled after the call iff the
  // corresponding in-vertex lies in the second (sink) partition.
  //
  // The out-vertices represent the liveness of the corresponding nodes. An
  // out-vertex lies in the first partition cannot be used after the call and
  // an out-vertex lies in the second partition can be used after the call. As
  // a result, if an in-vertex lies in the first partition and the out-vertex
  // lies in the second partition, the corresponding node needs to be spilt
  // before the call.
  //
  // In conclusion, the problem can be modelled as a minimum-cut problem.

  Node* call = find_first_call();
  if (call == nullptr) {
    return true;
  }

  // Construct the graph
  assert(vertex_num * vertex_num == graph_edges.length(), "");
  for (int i = 0; i < graph_edges.length(); i++) {
    graph_edges.at(i) = 0;
  }
  // Live-in nodes
  for (Node* n : livein) {
    int n_idx = node_data.at(n->_idx).vertex_idx;
    assert(n_idx != -1, "");
    int edge_idx = src_idx * vertex_num + n_idx;
    graph_edges.at(edge_idx) = std::numeric_limits<double>::infinity();
  }
  // Live-out nodes
  for (Node* n : liveout) {
    int n_idx = node_data.at(n->_idx).vertex_idx;
    if (n_idx == -1) {
      continue;
    }
    int edge_idx = (n_idx + 1) * vertex_num + snk_idx;
    graph_edges.at(edge_idx) = std::numeric_limits<double>::infinity();
  }
  // The call must be in the first partition
  int call_idx = node_data.at(call->_idx).vertex_idx;
  assert(call_idx != -1, "");
  int call_in = src_idx * vertex_num + call_idx;
  graph_edges.at(call_in) = std::numeric_limits<double>::infinity();
  // All successors of the call must be in the second partition
  for (DUIterator_Fast imax, i = call->fast_outs(imax); i < imax; i++) {
    Node* out = call->fast_out(i);
    if (out->is_Phi()) {
      // A Phi in another block does not care, a Phi in this block goes backward
      // to the start of the block
      continue;
    }
    int out_idx = node_data.at(out->_idx).vertex_idx;
    if (out_idx == -1) {
      continue;
    }
    int call_out = out_idx * vertex_num + snk_idx;
    graph_edges.at(call_out) = std::numeric_limits<double>::infinity();
  }

  for (int i = start_idx; i < end_idx; i++) {
    Node* n = scheduled.at(i);
    int n_idx = node_data.at(n->_idx).vertex_idx;
    assert(n_idx != -1, "");
    // in cannot be after out
    int back_edge = (n_idx + 1) * vertex_num + n_idx;
    graph_edges.at(back_edge) = std::numeric_limits<double>::infinity();
    // Spill value
    if (n != call) {
      int forward_edge = n_idx * vertex_num + n_idx + 1;
      double spill_value;
      if (n->is_Mach() && must_clone[n->as_Mach()->ideal_Opcode()]) {
        // Flag cannot be spilt
        spill_value = std::numeric_limits<double>::infinity();
      } else {
        spill_value = SUnit::Pressure(n).total_pressure();
      }
      graph_edges.at(forward_edge) = spill_value;
    }
    // Other calls must be in the second partition
    if (n != call &&
        (n->is_MachCall() || (n->is_Mach() && n->as_Mach()->has_call()))) {
      int call_edge = n_idx * vertex_num + snk_idx;
      graph_edges.at(call_edge) = std::numeric_limits<double>::infinity();
    }

    for (uint i = 0; i < n->len(); i++) {
      Node* in = n->in(i);
      if (in == nullptr) {
        continue;
      }
      int in_idx = node_data.at(in->_idx).vertex_idx;
      if (in_idx == -1) {
        continue;
      }

      // A node cannot be scheduled before its predecessors
      int dep_edge = n_idx * vertex_num + in_idx;
      graph_edges.at(dep_edge) = std::numeric_limits<double>::infinity();
      // If a required successor is after the call, then the out-vertex of the
      // node must be in the second partition
      if (i < n->req()) {
        int use_edge = (in_idx + 1) * vertex_num + n_idx;
        graph_edges.at(use_edge) = std::numeric_limits<double>::infinity();
      }
      // A Proj cannot be separate from its predecessors except when the main
      // node is the call we are scheduling
      if (in != call && n->is_Proj()) {
        int dep_edge = in_idx * vertex_num + n_idx;
        graph_edges.at(dep_edge) = std::numeric_limits<double>::infinity();
      }
      // A MachTemp cannot be separated from its successor
      if (in->is_MachTemp()) {
        int dep_edge = in_idx * vertex_num + n_idx;
        graph_edges.at(dep_edge) = std::numeric_limits<double>::infinity();
      }
    }
  }

  // Ford-Fulkerson algorithm
  GrowableArray<int> prev(vertex_num);
  GrowableArray<double> path_weights(vertex_num);
  GrowableArray<int> queue;
  while (true) {
    bfs(prev, path_weights, vertex_num, graph_edges, src_idx, snk_idx, queue);
    if (prev.at(snk_idx) == -1) {
      break;
    }

    double weight = path_weights.at(snk_idx);
    // Unschedulable (a flag cannot go with its use)
    if (weight == std::numeric_limits<double>::infinity()) {
      return false;
    }
    for (int second = snk_idx, first = -1; second != src_idx; second = first) {
      first = prev.at(second);
      graph_edges.at(first * vertex_num + second) -= weight;
      graph_edges.at(second * vertex_num + first) += weight;
    }
  }

  // No sink, just find the connected component
  bfs(prev, path_weights, vertex_num, graph_edges, src_idx, -1, queue);

  GrowableArray<Node*> new_scheduled(end_idx - start_idx);
  for (int i = 0; i < start_idx; i++) {
    new_scheduled.append(scheduled.at(i));
  }
  for (int i = start_idx; i < end_idx; i++) {
    Node* n = scheduled.at(i);
    if (n == call) {
      continue;
    }
    int idx = node_data.at(n->_idx).vertex_idx;
    if (prev.at(idx) != -1) {
      new_scheduled.append(n);
    }
  }

  // Schedule the call
  int temp_num = 0;
  for (uint i = 0; i < call->req(); i++) {
    Node* in = call->in(i);
    if (in != nullptr && in->is_MachTemp()) {
      assert(prev.at(node_data.at(in->_idx).vertex_idx) != -1, "");
      temp_num++;
      new_scheduled.remove(in);
      new_scheduled.append(in);
    }
  }
  GrowableArray<Node*> next_livein;
  bounds.append(new_scheduled.length() - temp_num);
  new_scheduled.append(call);
  next_livein.append(call);
  for (DUIterator_Fast imax, i = call->fast_outs(imax); i < imax; i++) {
    Node* out = call->fast_out(i);
    if (out->is_Proj()) {
      new_scheduled.append(out);
      next_livein.append(out);
      // Set to an arbitrary value so that we know which node has not been added
      int out_idx = node_data.at(out->_idx).vertex_idx;
      prev.at(out_idx) = 0;
    }
  }

  int next_start_idx = new_scheduled.length();
  bounds.append(next_start_idx);
  for (int i = start_idx; i < end_idx; i++) {
    Node* n = scheduled.at(i);
    int n_idx = node_data.at(n->_idx).vertex_idx;
    if (prev.at(n_idx) == -1) {
      new_scheduled.append(n);
    }
  }
  assert(new_scheduled.length() == end_idx, "");
  for (int i = start_idx; i < end_idx; i++) {
    Node* n = new_scheduled.at(i);
    scheduled.at(i) = n;
    node_data.at(n->_idx).idx_in_sched = i;
  }

  return schedule_calls_helper(scheduled, next_start_idx, end_idx,
                               bounds, next_livein, liveout, node_data,
                               vertex_num, graph_edges, src_idx, snk_idx);
}

static bool schedule_calls(const Block& block, GrowableArrayView<Node*>& scheduled,
                           GrowableArray<int>& bounds,
                           const GrowableArrayView<Node*>& livein,
                           const GrowableArrayView<Node*>& liveout,
                           GrowableArray<PhaseLCM::NodeData>& node_data) {
  int vertex_num = 0;
  for (int i = 0; i < scheduled.length(); i++) {
    Node* n = scheduled.at(i);
    assert(node_data.at(n->_idx).idx_in_sched == i, "");
    node_data.at(n->_idx).vertex_idx = vertex_num;
    vertex_num += 2;
  }
  int src_idx = vertex_num;
  int snk_idx = vertex_num + 1;
  vertex_num += 2;
  for (Node* n : livein) {
    node_data.at(n->_idx).vertex_idx = vertex_num;
    vertex_num += 2;
  }

  GrowableArray<double> graph_edges(vertex_num * vertex_num);
  graph_edges.at_grow(vertex_num * vertex_num - 1);
  bounds.clear();

  Node* end = block.end();
  if (end->is_Catch()) {
    // The block is dishonest, there can be no nodes between a CatchNode and its
    // corresponding call. This is fixed after LCM but the code there does not
    // take into consideration that derived pointers must go with their bases.
    // We try to avoid this bug by scheduling all nodes before the call except
    // those which depend on the call.
    // TODO: PROPERLY FIX THE ISSUE
    GrowableArray<Node*> worklist(scheduled.length());
    Node* call = end->in(0)->in(0);
    int &call_idx = node_data.at(call->_idx).idx_in_sched;
    call_idx = -1;
    worklist.append(call);
    while (!worklist.is_empty()) {
      int idx = worklist.length() - 1;
      Node* curr = worklist.at(idx);
      worklist.remove_at(idx);
      for (DUIterator_Fast imax, i = curr->fast_outs(imax); i < imax; i++) {
        Node* out = curr->fast_out(i);
        if (out == call) {
          // Cycle
          return false;
        }
        int& out_idx = node_data.at(out->_idx).idx_in_sched;
        if (out_idx != -1) {
          out_idx = -1;
          worklist.append(out);
        }
      }
      for (uint i = 0; i < curr->req(); i++) {
        Node* in = curr->in(i);
        if (in == nullptr) {
          continue;
        }
        if (in->is_MachTemp() ||
            (in->is_Mach() && must_clone[in->as_Mach()->ideal_Opcode()])) {
          int& in_idx = node_data.at(in->_idx).idx_in_sched;
          if (in_idx != -1) {
            in_idx = -1;
            worklist.append(in);
          }
        }
      }
    }

    // Use worklist to store new_scheduled
    worklist.clear();
    for (Node* n : scheduled) {
      int& idx = node_data.at(n->_idx).idx_in_sched;
      if (idx >= 0) {
        idx = worklist.length();
        worklist.append(n);
      }
    }

#ifdef ASSERT
    for (uint i = 0; i < call->req(); i++) {
      Node* in = call->in(i);
      assert(in == nullptr || !in->is_MachTemp(),
             "A call should not have MachTemp inputs");
    }
#endif // ASSERT
    call_idx = worklist.length();
    worklist.append(call);
    for (DUIterator_Fast imax, i = call->fast_outs(imax); i < imax; i++) {
      Node* out = call->fast_out(i);
      if (out->is_Proj()) {
        node_data.at(out->_idx).idx_in_sched = worklist.length();
        worklist.append(out);
      }
    }
    int after_call_idx = worklist.length();
    for (Node* n : scheduled) {
      int& idx = node_data.at(n->_idx).idx_in_sched;
      if (idx == -1) {
        idx = worklist.length();
        worklist.append(n);
      }
    }

    assert(worklist.length() == scheduled.length(), "");
    for (int i = 0; i < scheduled.length(); i++) {
      scheduled.at(i) = worklist.at(i);
    }

    // Now use worklist to store live nodes information
    worklist.clear();
    for (uint i = 0; i < call->req(); i++) {
      Node* in = call->in(i);
      if (in != nullptr) {
        worklist.append(in);
      }
    }

    bounds.append(0);
    bool success = true;
    if (!StressLCM && OptoRegScheduling) {
      success = schedule_calls_helper(scheduled, 0, call_idx,
                                      bounds, livein, worklist, node_data,
                                      vertex_num, graph_edges, src_idx, snk_idx);
    }
    if (!success) {
      return false;
    }

    bounds.append(call_idx);

    worklist.clear();
    worklist.append(call);
    for (DUIterator_Fast imax, i = call->fast_outs(imax); i < imax; i++) {
      Node* out = call->fast_out(i);
      if (out->is_Proj()) {
        worklist.append(out);
      }
    }
    bounds.append(after_call_idx);

    if (!StressLCM && OptoRegScheduling) {
      success = schedule_calls_helper(scheduled, after_call_idx, scheduled.length(),
                                      bounds, worklist, liveout, node_data,
                                      vertex_num, graph_edges, src_idx, snk_idx);
    }
    bounds.append(scheduled.length());
    return success;
  } else {
    bounds.append(0);
    bool success = true;
    if (!StressLCM && OptoRegScheduling) {
      success = schedule_calls_helper(scheduled, 0, scheduled.length(),
                                      bounds, livein, liveout, node_data,
                                      vertex_num, graph_edges, src_idx, snk_idx);
    }
    bounds.append(scheduled.length());
    return success;
  }
}

static void add_call_projs(PhaseCFG& cfg, const Matcher& matcher, Block& block) {
  // Fill in the kill mask for the call
  auto add_call_kills = [](MachProjNode *proj, RegMask& regs,
                           const char* save_policy, bool exclude_soe) {
    for (OptoReg::Name r = OptoReg::Name(0); r < _last_Mach_Reg; r = OptoReg::add(r, 1)) {
      if (!regs.Member(r)) {
        // Not already defined by the call
        if ((save_policy[r] == 'C') ||
            (save_policy[r] == 'A') ||
            ((save_policy[r] == 'E') && exclude_soe)) {
          proj->_rout.Insert(r);
        }
      }
    }
  };

  for (int idx = block.number_of_nodes() - 1; idx >= 0; idx--) {
    Node* n = block.get_node(idx);
    if (n->is_MachCall()) {
      MachCallNode* call = n->as_MachCall();
      RegMask regs;

      // Collect all the defined registers.
      for (DUIterator_Fast imax, i = call->fast_outs(imax); i < imax; i++) {
        Node* out = call->fast_out(i);
        assert(out->is_MachProj(), "");
        regs.OR(out->out_RegMask());
      }

      // Act as if the call defines the Frame Pointer.
      // Certainly the FP is alive and well after the call.
      regs.Insert(matcher.c_frame_pointer());

      // Set all registers killed and not already defined by the call.
      uint r_cnt = call->tf()->range()->cnt();
      int op = call->ideal_Opcode();
      MachProjNode* proj = new MachProjNode(call, r_cnt + 1, RegMask::Empty, MachProjNode::fat_proj);
      cfg.map_node_to_block(proj, &block);
      block.insert_node(proj, idx + 1);

      // Select the right register save policy.
      const char* save_policy = nullptr;
      switch (op) {
        case Op_CallRuntime:
        case Op_CallLeaf:
        case Op_CallLeafNoFP:
        case Op_CallLeafVector:
          // Calling C code so use C calling convention
          save_policy = matcher._c_reg_save_policy;
          break;

        case Op_CallStaticJava:
        case Op_CallDynamicJava:
          // Calling Java code so use Java calling convention
          save_policy = matcher._register_save_policy;
          break;

        default:
          ShouldNotReachHere();
      }

      // When using CallRuntime mark SOE registers as killed by the call
      // so values that could show up in the RegisterMap aren't live in a
      // callee saved register since the register wouldn't know where to
      // find them.  CallLeaf and CallLeafNoFP are ok because they can't
      // have debug info on them.  Strictly speaking this only needs to be
      // done for oops since idealreg2debugmask takes care of debug info
      // references but there no way to handle oops differently than other
      // pointers as far as the kill mask goes.
      bool exclude_soe = op == Op_CallRuntime;

      // If the call is a MethodHandle invoke, we need to exclude the
      // register which is used to save the SP value over MH invokes from
      // the mask.  Otherwise this register could be used for
      // deoptimization information.
      if (op == Op_CallStaticJava) {
        MachCallStaticJavaNode* static_call = (MachCallStaticJavaNode*) call;
        if (static_call->_method_handle_invoke) {
          proj->_rout.OR(Matcher::method_handle_invoke_SP_save_mask());
        }
      }

      add_call_kills(proj, regs, save_policy, exclude_soe);
    } else if (n->is_Mach() && n->as_Mach()->has_call()) {
      RegMask regs;
      regs.Insert(matcher.c_frame_pointer());
      regs.OR(n->out_RegMask());

      MachProjNode* proj = new MachProjNode(n, 1, RegMask::Empty, MachProjNode::fat_proj);
      cfg.map_node_to_block(proj, &block);
      block.insert_node(proj, idx + 1);

      add_call_kills(proj, regs, matcher._c_reg_save_policy, false);
    }
  }
}

SBlock::SBlock(GrowableArrayView<Node*>& scheduled, int start_idx, int end_idx,
               GrowableArrayView<PhaseLCM::NodeData>& node_data)
  : _scheduled(scheduled), _start_idx(start_idx), _end_idx(end_idx),
    _sink(nullptr), _node_data(node_data) {
  for (int i = start_idx; i < end_idx; i++) {
    Node* n = scheduled.at(i);
    SUnit* unit = SUnit::try_create(n, node_data
                                    DEBUG_ONLY(COMMA start_idx COMMA end_idx));
    if (unit != nullptr) {
      _units.append(unit);
    }
  }

#ifdef ASSERT
  for (int i = start_idx; i < end_idx; i++) {
    Node* n = scheduled.at(i);
    SUnit* unit = _node_data.at(n->_idx).sunit;
    assert(unit != nullptr && _units.contains(unit), "a node must belong to a unit");
  }
#endif // ASSERT

  for (SUnit* unit : _units) {
    unit->add_predecessors(*this, node_data);
  }
  _sink = SUnit::create_sink(*this, _units);
  _units.append(_sink);
  if (!StressLCM && OptoRegScheduling) {
    SUnit::calculate_sethi_ullman_numbers(_sink);
#ifdef ASSERT
    for (SUnit* unit : _units) {
      assert(unit->has_sethi_ullman(), "must be reachable from sink");
    }
#endif // ASSERT
  }
}

template <class F>
bool SBlock::schedule(F random) {
  GrowableArray<SUnit*> worklist(_units.length());
  GrowableArray<SUnit*> result(_units.length());
  worklist.append(_sink);
  while (!worklist.is_empty()) {
    int idx;
    if (StressLCM) {
      idx = random() % worklist.length();
    } else {
      idx = worklist.length() - 1;
    }
    SUnit* curr = worklist.at(idx);
    worklist.remove_at(idx);
    result.append(curr);
    curr->schedule(worklist);
  }
  if (result.length() != _units.length()) {
    // Cycle
    return false;
  }

  Node** curr = _scheduled.adr_at(_start_idx);
  for (int i = result.length() - 1; i >= 0; i--) {
    curr = result.at(i)->expand(curr);
  }
  assert(curr == _scheduled.adr_at(0) + _end_idx, "");
  return true;
}

bool SBlock::contains(const Node* n) const {
  int idx = _node_data.at(n->_idx).idx_in_sched;
  return idx >= _start_idx && idx < _end_idx;
}

SUnit::SUnit(Node* n, GrowableArrayView<PhaseLCM::NodeData>& node_data
#ifdef ASSERT
           , int start_idx, int end_idx
#endif // ASSERT
) : _def(n), _sethi_ullman(SethiUllmanStatus::not_calculated), _unsched_outs(0) {
  auto add_node = [&](Node* m) {
    int idx = node_data.at(m->_idx).idx_in_sched;
    assert(idx >= start_idx && idx < end_idx, "must be together");
    if (idx >= 0) {
      _nodes.append(m);
    }
  };

  for (uint i = 0; i < n->req(); i++) {
    Node* in = n->in(i);
    if (in != nullptr && in->is_MachTemp()) {
      _temp_pressure = _temp_pressure.add(Pressure(in));
      add_node(in);
    }
  }

  add_node(n);
  _out_pressure = Pressure(n);

  for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
    Node* out = n->fast_out(i);
    if (out->is_Proj()) {
      add_node(out);
      _out_pressure = _out_pressure.add(Pressure(out));
    }
  }
}

SUnit* SUnit::try_create(Node* n, GrowableArrayView<PhaseLCM::NodeData>& node_data
#ifdef ASSERT
                       , int start_idx, int end_idx
#endif // ASSERT
) {
  // It is theoretically possible to schedule flags independently but it would
  // be easier to stick them with their successors
  if (n->is_MachTemp() || n->is_Proj() ||
      (n->is_Mach() && must_clone[n->as_Mach()->ideal_Opcode()])) {
    return nullptr;
  }

  SUnit* unit = new SUnit(n, node_data
                          DEBUG_ONLY(COMMA start_idx COMMA end_idx));

  // Schedule flags with their successors
  Node_List worklist;
  worklist.push(n);
  while (worklist.size() > 0) {
    Node* child = worklist.pop();
    for (uint i = 0; i < child->req(); i++) {
      Node* in = child->in(i);
      if (in == nullptr || !in->is_Mach()) {
        continue;
      }
      if (must_clone[in->as_Mach()->ideal_Opcode()]) {
#ifdef ASSERT
        int idx = node_data.at(in->_idx).idx_in_sched;
        assert(idx >= start_idx && idx < end_idx, "flags must come with its successor");
#endif // ASSERT
        SUnit* pred_unit = new SUnit(in, node_data
                                     DEBUG_ONLY(COMMA start_idx COMMA end_idx));
        unit->_nodes.insert_before(0, &pred_unit->_nodes);
        unit->_temp_pressure = unit->_temp_pressure.componentwise_max(pred_unit->_temp_pressure);
        unit->_out_pressure = unit->_out_pressure.componentwise_max(pred_unit->_out_pressure);
        worklist.push(in);
      }
    }
  }

  for (const Node* n : unit->_nodes) {
    assert(node_data.at(n->_idx).sunit == nullptr, "A Node can only belong to 1 SUnit");
    node_data.at(n->_idx).sunit = unit;
  }

  return unit;
}

SUnit* SUnit::create_sink(const SBlock& block, const GrowableArrayView<SUnit*>& units) {
  SUnit* sink = new SUnit();
  for (SUnit* unit : units) {
    Pressure p;
    for (Node* n : unit->_nodes) {
      for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
        Node* out = n->fast_out(i);
        if (block.contains(out)) {
          continue;
        }

        p = p.add(Pressure(n));
        break;
      }
    }
    if (unit->_unsched_outs == 0 || p.total_pressure() > 0) {
      SDep* dep = new SDep(unit, sink, p);
      sink->_preds.append(dep);
      unit->_succs.append(dep);
      unit->_unsched_outs++;
    }
  }
  return sink;
}

template <class F>
static SUnit::Pressure calculate_input_sethi_ullman(SUnit::SDep** inputs, int n,
                                                    F sethi_ullman_getter) {
  assert(n > 0, "");
  constexpr int max_exhaustive = 6;
  if (n == 1) {
    return sethi_ullman_getter(inputs[0]->pred());
  } else if (n > max_exhaustive) {
    SUnit::Pressure max = sethi_ullman_getter(inputs[0]->pred());
    SUnit::SDep** max_ele = &inputs[0];
    for (int i = 1; i < n; i++) {
      SUnit::Pressure curr = sethi_ullman_getter(inputs[i]->pred());
      if (max.less_than(curr)) {
        max = curr;
        max_ele = &inputs[i];
      }
    }
    swap(inputs[0], *max_ele);
    SUnit::Pressure suffix =
      calculate_input_sethi_ullman(inputs + 1, n - 1, sethi_ullman_getter);
    return sethi_ullman_getter(inputs[0]->pred())
      .componentwise_max(inputs[0]->pressure().add(suffix));
  }

  size_t input_size = sizeof(SUnit::SDep*) * n;
  SUnit::SDep* temp[max_exhaustive];
  SUnit::SDep* curr[max_exhaustive];
  auto helper = [&]() {
    SUnit::Pressure suffix =
      calculate_input_sethi_ullman(temp + 1, n - 1, sethi_ullman_getter);
    return sethi_ullman_getter(temp[0]->pred())
      .componentwise_max(temp[0]->pressure().add(suffix));
  };
  memcpy(temp, inputs, input_size);
  SUnit::Pressure min = helper();
  memcpy(curr, temp, input_size);
  for (int i = 1; i < n; i++) {
    memcpy(temp, inputs, input_size);
    swap(temp[0], temp[i]);
    SUnit::Pressure p = helper();
    if (p.less_than(min)) {
      min = p;
      memcpy(curr, temp, input_size);
    }
  }
  memcpy(inputs, curr, input_size);
  return min;
}

void SUnit::calculate_sethi_ullman_numbers(SUnit* root) {
  if (root->_sethi_ullman == SethiUllmanStatus::calculated) {
    return;
  }

  GrowableArray<SUnit*> worklist;
  worklist.append(root);
  while (!worklist.is_empty()) {
    SUnit* curr = worklist.at(worklist.length() - 1);
    if (curr->_sethi_ullman == SethiUllmanStatus::calculated) {
      worklist.remove_at(worklist.length() - 1);
      continue;
    }

    curr->_sethi_ullman = SethiUllmanStatus::calculating;
    bool wait_for_input = false;
    for (SDep* dep : curr->_preds) {
      SUnit* pred = dep->pred();
      if (pred != nullptr &&
          pred->_sethi_ullman == SethiUllmanStatus::not_calculated) {
        wait_for_input = true;
        worklist.append(pred);
      }
    }
    if (wait_for_input) {
      continue;
    }

    worklist.remove_at(worklist.length() - 1);
    for (int i = 1; i < curr->_preds.length(); i++) {
      if (curr->_preds.at(i)->pred() == nullptr) {
        // Inputs not in this block must be scheduled first
        swap(curr->_preds.at(0), curr->_preds.at(i));
        break;
      }
    }

    Pressure input;
    int has_null_pred = 0;
    if (curr->_preds.at(0)->pred() == nullptr) {
      has_null_pred = 1;
      input = curr->_preds.at(0)->pressure();
    }
    if (curr->_preds.length() - has_null_pred > 0) {
      auto sethi_ullman_getter = [](SUnit* unit) {
        return unit->_sethi_ullman_value;
      };
      Pressure suffix = calculate_input_sethi_ullman(curr->_preds.adr_at(has_null_pred),
                                                     curr->_preds.length() - has_null_pred,
                                                     sethi_ullman_getter);
      input = input.add(suffix);
    }

    Pressure in(curr->_temp_pressure);
    for (SDep* dep : curr->_preds) {
      in.add(dep->pressure());
    }
    Pressure total = input.componentwise_max(in).componentwise_max(curr->_out_pressure);

    curr->_sethi_ullman_value = total;
    curr->_sethi_ullman = SethiUllmanStatus::calculated;
  }
}

void SUnit::add_predecessors(const SBlock& block,
                             const GrowableArrayView<PhaseLCM::NodeData>& node_data) {
  GrowableArray<const Node*> input_nodes;
  for (const Node* n : _nodes) {
    assert(block.contains(n), "");
    for (uint i = 0; i < n->len(); i++) {
      Node* in = n->in(i);
      if (in == nullptr || input_nodes.contains(in)) {
        continue;
      }
      input_nodes.append(in);

      Pressure p;
      if (i < n->req()) {
        p = Pressure(in);
      }

      SUnit* in_unit = nullptr;
      if (block.contains(in)) {
        in_unit = node_data.at(in->_idx).sunit;
      }
      if (in_unit == this) {
        continue;
      }

      bool existed = false;
      for (int i = 0; i < _preds.length(); i++) {
        SDep* dep = _preds.at(i);
        if (dep->pred() == in_unit) {
          existed = true;
          dep->add_pressure(p);
          break;
        }
      }
      if (existed) {
        continue;
      }

      SDep* dep = new SDep(in_unit, this, p);
      _preds.append(dep);
      if (in_unit != nullptr) {
        in_unit->_succs.append(dep);
        in_unit->_unsched_outs++;
      }
    }
  }
}

void SUnit::schedule(GrowableArray<SUnit*>& worklist) {
  for (int i = 0; i < _preds.length(); i++) {
    SDep* dep = _preds.at(i);
    if (dep->pred() != nullptr) {
      int& unsched_outs = dep->pred()->_unsched_outs;
      assert(unsched_outs > 0, "");
      unsched_outs--;
      if (unsched_outs == 0) {
        worklist.append(dep->pred());
      }
    }
  }
}

Node** SUnit::expand(Node** start) const {
  if (_nodes.is_empty()) {
    return start;
  }
  memcpy(start, _nodes.adr_at(0), sizeof(Node*) * _nodes.length());
  return start + _nodes.length();
}

GrowableArray<Node*> SUnit::expand() const {
  GrowableArray<Node*> res;
  if (_nodes.is_empty()) {
    return res;
  }
  res.at_grow(_nodes.length() - 1);
  memcpy(res.adr_at(0), _nodes.adr_at(0), sizeof(Node*) * _nodes.length());
  return res;
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

SUnit::Pressure SUnit::Pressure::add(const Pressure& other) const {
  return Pressure(_int + other._int, _float + other._float, _mask + other._mask);
}

SUnit::Pressure SUnit::Pressure::componentwise_max(const Pressure& other) const {
  return Pressure(MAX2(_int, other._int), MAX2(_float, other._float),
                  MAX2(_mask, other._mask));
}

bool SUnit::Pressure::less_than(const Pressure& other) const {
  constexpr size_t component_num = 3;
  auto sort3 = [](int (&a)[component_num], int x, int y, int z) {
    if (x < y) {
      if (y < z) {
        a[0] = z;
        a[1] = y;
        a[2] = x;
      } else if (x < z) {
        a[0] = y;
        a[1] = z;
        a[2] = x;
      } else {
        a[0] = y;
        a[1] = x;
        a[2] = z;
      }
    } else {
      if (x < z) {
        a[0] = z;
        a[1] = x;
        a[2] = y;
      } else if (y < z) {
        a[0] = x;
        a[1] = z;
        a[2] = y;
      } else {
        a[0] = x;
        a[1] = y;
        a[2] = z;
      }
    }
  };

  int p1_data[component_num];
  int p2_data[component_num];
  sort3(p1_data, _int, _float, _mask);
  sort3(p2_data, other._int, other._float, other._mask);
  for (size_t i = 0; i < component_num; i++) {
    if (p1_data[i] < p2_data[i]) {
      return true;
    } else if (p1_data[i] > p2_data[i]) {
      return false;
    }
  }
  return false;
}

#ifndef PRODUCT
void SBlock::dump() {
  for (SUnit* u : _units) {
    tty->print("# ");
    u->dump();
  }
  tty->print_cr("#");
}

void SUnit::dump() {
  auto print_pressure = [](const Pressure& p) {
    tty->print("{I:%d F:%d M:%d}", p._int, p._float, p._mask);
  };
  if (_def == nullptr) {
    tty->print("0  Sink  === ");
  } else {
    _def->dump_idx(true);
    tty->print("  ");
    _def->dump_name();
    tty->print("  === ");
  }

  for (int i = 0; i < _preds.length(); i++) {
    SDep* dep = _preds.at(i);
    SUnit* pred = dep->pred();
    if (pred == nullptr) {
      tty->print("_ ");
    } else {
      pred->_def->dump_idx();
      tty->print(" ");
    }

    print_pressure(dep->pressure());
    if (i != _preds.length() - 1) {
      tty->print(", ");
    }
  }

  tty->print(" [[ ");
  for (int i = 0; i < _succs.length(); i++) {
    SDep* dep = _succs.at(i);
    if (dep->succ()->_def == nullptr) {
      tty->print("0 ");
    } else {
      dep->succ()->_def->dump_idx();
      tty->print(" ");
    }
  }

  tty->print(" ]] temp: ");
  print_pressure(_temp_pressure);
  tty->print(" out: ");
  print_pressure(_out_pressure);
  tty->print(" sethi-ullman: ");
  print_pressure(_sethi_ullman_value);
  tty->cr();
}
#endif // PRODUCT
