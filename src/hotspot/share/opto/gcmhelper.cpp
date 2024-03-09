/*
 * Copyright (c) 1998, 2024, Oracle and/or its affiliates. All rights reserved.
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
#include "runtime/os.inline.hpp"

// Optimization - Graph Style

// Check whether val is not-null-decoded compressed oop,
// i.e. will grab into the base of the heap if it represents null.
static bool accesses_heap_base_zone(Node *val) {
  if (CompressedOops::base() != nullptr) { // Implies UseCompressedOops.
    if (val && val->is_Mach()) {
      if (val->as_Mach()->ideal_Opcode() == Op_DecodeN) {
        // This assumes all Decodes with TypePtr::NotNull are matched to nodes that
        // decode null to point to the heap base (Decode_NN).
        if (val->bottom_type()->is_oopptr()->ptr() == TypePtr::NotNull) {
          return true;
        }
      }
      // Must recognize load operation with Decode matched in memory operand.
      // We should not reach here except for PPC/AIX, as os::zero_page_read_protected()
      // returns true everywhere else. On PPC, no such memory operands
      // exist, therefore we did not yet implement a check for such operands.
      NOT_AIX(Unimplemented());
    }
  }
  return false;
}

static bool needs_explicit_null_check_for_read(Node *val) {
  // On some OSes (AIX) the page at address 0 is only write protected.
  // If so, only Store operations will trap.
  if (os::zero_page_read_protected()) {
    return false;  // Implicit null check will work.
  }
  // Also a read accessing the base of a heap-based compressed heap will trap.
  if (accesses_heap_base_zone(val) &&         // Hits the base zone page.
      CompressedOops::use_implicit_null_checks()) { // Base zone page is protected.
    return false;
  }

  return true;
}

//------------------------------implicit_null_check----------------------------
// Detect implicit-null-check opportunities.  Basically, find null checks
// with suitable memory ops nearby.  Use the memory op to do the null check.
// I can generate a memory op if there is not one nearby.
// The proj is the control projection for the not-null case.
// The val is the pointer being checked for nullness or
// decodeHeapOop_not_null node if it did not fold into address.
void PhaseCFG::implicit_null_check(Block* block, Node *proj, Node *val, int allowed_reasons) {
  // Assume if null check need for 0 offset then always needed
  // Intel solaris doesn't support any null checks yet and no
  // mechanism exists (yet) to set the switches at an os_cpu level
  if( !ImplicitNullChecks || MacroAssembler::needs_explicit_null_check(0)) return;

  // Make sure the ptr-is-null path appears to be uncommon!
  float f = block->end()->as_MachIf()->_prob;
  if( proj->Opcode() == Op_IfTrue ) f = 1.0f - f;
  if( f > PROB_UNLIKELY_MAG(4) ) return;

  uint bidx = 0;                // Capture index of value into memop
  bool was_store;               // Memory op is a store op

  // Get the successor block for if the test ptr is non-null
  Block* not_null_block;  // this one goes with the proj
  Block* null_block;
  if (block->get_node(block->number_of_nodes()-1) == proj) {
    null_block     = block->_succs[0];
    not_null_block = block->_succs[1];
  } else {
    assert(block->get_node(block->number_of_nodes()-2) == proj, "proj is one or the other");
    not_null_block = block->_succs[0];
    null_block     = block->_succs[1];
  }
  while (null_block->is_Empty() == Block::empty_with_goto) {
    null_block     = null_block->_succs[0];
  }

  // Search the exception block for an uncommon trap.
  // (See Parse::do_if and Parse::do_ifnull for the reason
  // we need an uncommon trap.  Briefly, we need a way to
  // detect failure of this optimization, as in 6366351.)
  {
    bool found_trap = false;
    for (uint i1 = 0; i1 < null_block->number_of_nodes(); i1++) {
      Node* nn = null_block->get_node(i1);
      if (nn->is_MachCall() &&
          nn->as_MachCall()->entry_point() == SharedRuntime::uncommon_trap_blob()->entry_point()) {
        const Type* trtype = nn->in(TypeFunc::Parms)->bottom_type();
        if (trtype->isa_int() && trtype->is_int()->is_con()) {
          jint tr_con = trtype->is_int()->get_con();
          Deoptimization::DeoptReason reason = Deoptimization::trap_request_reason(tr_con);
          Deoptimization::DeoptAction action = Deoptimization::trap_request_action(tr_con);
          assert((int)reason < (int)BitsPerInt, "recode bit map");
          if (is_set_nth_bit(allowed_reasons, (int) reason)
              && action != Deoptimization::Action_none) {
            // This uncommon trap is sure to recompile, eventually.
            // When that happens, C->too_many_traps will prevent
            // this transformation from happening again.
            found_trap = true;
          }
        }
        break;
      }
    }
    if (!found_trap) {
      // We did not find an uncommon trap.
      return;
    }
  }

  // Check for decodeHeapOop_not_null node which did not fold into address
  bool is_decoden = ((intptr_t)val) & 1;
  val = (Node*)(((intptr_t)val) & ~1);

  assert(!is_decoden ||
         ((val->in(0) == nullptr) && val->is_Mach() &&
          (val->as_Mach()->ideal_Opcode() == Op_DecodeN)), "sanity");

  // Search the successor block for a load or store who's base value is also
  // the tested value.  There may be several.
  MachNode *best = nullptr;        // Best found so far
  for (DUIterator i = val->outs(); val->has_out(i); i++) {
    Node *m = val->out(i);
    if( !m->is_Mach() ) continue;
    MachNode *mach = m->as_Mach();
    was_store = false;
    int iop = mach->ideal_Opcode();
    switch( iop ) {
    case Op_LoadB:
    case Op_LoadUB:
    case Op_LoadUS:
    case Op_LoadD:
    case Op_LoadF:
    case Op_LoadI:
    case Op_LoadL:
    case Op_LoadP:
    case Op_LoadN:
    case Op_LoadS:
    case Op_LoadKlass:
    case Op_LoadNKlass:
    case Op_LoadRange:
    case Op_LoadD_unaligned:
    case Op_LoadL_unaligned:
      assert(mach->in(2) == val, "should be address");
      break;
    case Op_StoreB:
    case Op_StoreC:
    case Op_StoreCM:
    case Op_StoreD:
    case Op_StoreF:
    case Op_StoreI:
    case Op_StoreL:
    case Op_StoreP:
    case Op_StoreN:
    case Op_StoreNKlass:
      was_store = true;         // Memory op is a store op
      // Stores will have their address in slot 2 (memory in slot 1).
      // If the value being nul-checked is in another slot, it means we
      // are storing the checked value, which does NOT check the value!
      if( mach->in(2) != val ) continue;
      break;                    // Found a memory op?
    case Op_StrComp:
    case Op_StrEquals:
    case Op_StrIndexOf:
    case Op_StrIndexOfChar:
    case Op_AryEq:
    case Op_VectorizedHashCode:
    case Op_StrInflatedCopy:
    case Op_StrCompressedCopy:
    case Op_EncodeISOArray:
    case Op_CountPositives:
      // Not a legit memory op for implicit null check regardless of
      // embedded loads
      continue;
    default:                    // Also check for embedded loads
      if( !mach->needs_anti_dependence_check() )
        continue;               // Not an memory op; skip it
      if( must_clone[iop] ) {
        // Do not move nodes which produce flags because
        // RA will try to clone it to place near branch and
        // it will cause recompilation, see clone_node().
        continue;
      }
      {
        // Check that value is used in memory address in
        // instructions with embedded load (CmpP val1,(val2+off)).
        Node* base;
        Node* index;
        const MachOper* oper = mach->memory_inputs(base, index);
        if (oper == nullptr || oper == (MachOper*)-1) {
          continue;             // Not an memory op; skip it
        }
        if (val == base ||
            (val == index && val->bottom_type()->isa_narrowoop())) {
          break;                // Found it
        } else {
          continue;             // Skip it
        }
      }
      break;
    }

    // On some OSes (AIX) the page at address 0 is only write protected.
    // If so, only Store operations will trap.
    // But a read accessing the base of a heap-based compressed heap will trap.
    if (!was_store && needs_explicit_null_check_for_read(val)) {
      continue;
    }

    // Check that node's control edge is not-null block's head or dominates it,
    // otherwise we can't hoist it because there are other control dependencies.
    Node* ctrl = mach->in(0);
    if (ctrl != nullptr && !(ctrl == not_null_block->head() ||
        get_block_for_node(ctrl)->dominates(not_null_block))) {
      continue;
    }

    // check if the offset is not too high for implicit exception
    {
      intptr_t offset = 0;
      const TypePtr *adr_type = nullptr;  // Do not need this return value here
      const Node* base = mach->get_base_and_disp(offset, adr_type);
      if (base == nullptr || base == NodeSentinel) {
        // Narrow oop address doesn't have base, only index.
        // Give up if offset is beyond page size or if heap base is not protected.
        if (val->bottom_type()->isa_narrowoop() &&
            (MacroAssembler::needs_explicit_null_check(offset) ||
             !CompressedOops::use_implicit_null_checks()))
          continue;
        // cannot reason about it; is probably not implicit null exception
      } else {
        const TypePtr* tptr;
        if ((UseCompressedOops || UseCompressedClassPointers) &&
            (CompressedOops::shift() == 0 || CompressedKlassPointers::shift() == 0)) {
          // 32-bits narrow oop can be the base of address expressions
          tptr = base->get_ptr_type();
        } else {
          // only regular oops are expected here
          tptr = base->bottom_type()->is_ptr();
        }
        // Give up if offset is not a compile-time constant.
        if (offset == Type::OffsetBot || tptr->_offset == Type::OffsetBot)
          continue;
        offset += tptr->_offset; // correct if base is offsetted
        // Give up if reference is beyond page size.
        if (MacroAssembler::needs_explicit_null_check(offset))
          continue;
        // Give up if base is a decode node and the heap base is not protected.
        if (base->is_Mach() && base->as_Mach()->ideal_Opcode() == Op_DecodeN &&
            !CompressedOops::use_implicit_null_checks())
          continue;
      }
    }

    // Check ctrl input to see if the null-check dominates the memory op
    Block *cb = get_block_for_node(mach);
    cb = cb->_idom;             // Always hoist at least 1 block
    if( !was_store ) {          // Stores can be hoisted only one block
      while( cb->_dom_depth > (block->_dom_depth + 1))
        cb = cb->_idom;         // Hoist loads as far as we want
      // The non-null-block should dominate the memory op, too. Live
      // range spilling will insert a spill in the non-null-block if it is
      // needs to spill the memory op for an implicit null check.
      if (cb->_dom_depth == (block->_dom_depth + 1)) {
        if (cb != not_null_block) continue;
        cb = cb->_idom;
      }
    }
    if( cb != block ) continue;

    // Found a memory user; see if it can be hoisted to check-block
    uint vidx = 0;              // Capture index of value into memop
    uint j;
    for( j = mach->req()-1; j > 0; j-- ) {
      if( mach->in(j) == val ) {
        vidx = j;
        // Ignore DecodeN val which could be hoisted to where needed.
        if( is_decoden ) continue;
      }
      // Block of memory-op input
      Block *inb = get_block_for_node(mach->in(j));
      Block *b = block;          // Start from nul check
      while( b != inb && b->_dom_depth > inb->_dom_depth )
        b = b->_idom;           // search upwards for input
      // See if input dominates null check
      if( b != inb )
        break;
    }
    if( j > 0 )
      continue;
    Block *mb = get_block_for_node(mach);
    // Hoisting stores requires more checks for the anti-dependence case.
    // Give up hoisting if we have to move the store past any load.
    if (was_store) {
       // Make sure control does not do a merge (would have to check allpaths)
       if (mb->num_preds() != 2) {
         continue;
       }
       // mach is a store, hence block is the immediate dominator of mb.
       // Due to the null-check shape of block (where its successors cannot re-join),
       // block must be the direct predecessor of mb.
       assert(get_block_for_node(mb->pred(1)) == block, "Unexpected predecessor block");
       uint k;
       uint num_nodes = mb->number_of_nodes();
       for (k = 1; k < num_nodes; k++) {
         Node *n = mb->get_node(k);
         if (n->needs_anti_dependence_check() &&
             n->in(LoadNode::Memory) == mach->in(StoreNode::Memory)) {
           break;              // Found anti-dependent load
         }
       }
       if (k < num_nodes) {
         continue;             // Found anti-dependent load
       }
    }

    // Make sure this memory op is not already being used for a NullCheck
    Node *e = mb->end();
    if( e->is_MachNullCheck() && e->in(1) == mach )
      continue;                 // Already being used as a null check

    // Found a candidate!  Pick one with least dom depth - the highest
    // in the dom tree should be closest to the null check.
    if (best == nullptr || get_block_for_node(mach)->_dom_depth < get_block_for_node(best)->_dom_depth) {
      best = mach;
      bidx = vidx;
    }
  }
  // No candidate!
  if (best == nullptr) {
    return;
  }

  // ---- Found an implicit null check
#ifndef PRODUCT
  extern uint implicit_null_checks;
  implicit_null_checks++;
#endif

  if( is_decoden ) {
    // Check if we need to hoist decodeHeapOop_not_null first.
    Block *valb = get_block_for_node(val);
    if( block != valb && block->_dom_depth < valb->_dom_depth ) {
      // Hoist it up to the end of the test block together with its inputs if they exist.
      for (uint i = 2; i < val->req(); i++) {
        // DecodeN has 2 regular inputs + optional MachTemp or load Base inputs.
        Node *temp = val->in(i);
        Block *tempb = get_block_for_node(temp);
        if (!tempb->dominates(block)) {
          assert(block->dominates(tempb), "sanity check: temp node placement");
          // We only expect nodes without further inputs, like MachTemp or load Base.
          assert(temp->req() == 0 || (temp->req() == 1 && temp->in(0) == (Node*)C->root()),
                 "need for recursive hoisting not expected");
          tempb->find_remove(temp);
          block->add_inst(temp);
          map_node_to_block(temp, block);
        }
      }
      valb->find_remove(val);
      block->add_inst(val);
      map_node_to_block(val, block);
      // DecodeN on x86 may kill flags. Check for flag-killing projections
      // that also need to be hoisted.
      for (DUIterator_Fast jmax, j = val->fast_outs(jmax); j < jmax; j++) {
        Node* n = val->fast_out(j);
        if( n->is_MachProj() ) {
          get_block_for_node(n)->find_remove(n);
          block->add_inst(n);
          map_node_to_block(n, block);
        }
      }
    }
  }
  // Hoist the memory candidate up to the end of the test block.
  Block *old_block = get_block_for_node(best);
  old_block->find_remove(best);
  block->add_inst(best);
  map_node_to_block(best, block);

  // Move the control dependence if it is pinned to not-null block.
  // Don't change it in other cases: null or dominating control.
  Node* ctrl = best->in(0);
  if (ctrl != nullptr && get_block_for_node(ctrl) == not_null_block) {
    // Set it to control edge of null check.
    best->set_req(0, proj->in(0)->in(0));
  }

  // Check for flag-killing projections that also need to be hoisted
  // Should be DU safe because no edge updates.
  for (DUIterator_Fast jmax, j = best->fast_outs(jmax); j < jmax; j++) {
    Node* n = best->fast_out(j);
    if( n->is_MachProj() ) {
      get_block_for_node(n)->find_remove(n);
      block->add_inst(n);
      map_node_to_block(n, block);
    }
  }

  // proj==Op_True --> ne test; proj==Op_False --> eq test.
  // One of two graph shapes got matched:
  //   (IfTrue  (If (Bool NE (CmpP ptr null))))
  //   (IfFalse (If (Bool EQ (CmpP ptr null))))
  // null checks are always branch-if-eq.  If we see a IfTrue projection
  // then we are replacing a 'ne' test with a 'eq' null check test.
  // We need to flip the projections to keep the same semantics.
  if( proj->Opcode() == Op_IfTrue ) {
    // Swap order of projections in basic block to swap branch targets
    Node *tmp1 = block->get_node(block->end_idx()+1);
    Node *tmp2 = block->get_node(block->end_idx()+2);
    block->map_node(tmp2, block->end_idx()+1);
    block->map_node(tmp1, block->end_idx()+2);
    Node *tmp = new Node(C->top()); // Use not null input
    tmp1->replace_by(tmp);
    tmp2->replace_by(tmp1);
    tmp->replace_by(tmp2);
    tmp->destruct(nullptr);
  }

  // Remove the existing null check; use a new implicit null check instead.
  // Since schedule-local needs precise def-use info, we need to correct
  // it as well.
  Node *old_tst = proj->in(0);
  MachNode *nul_chk = new MachNullCheckNode(old_tst->in(0),best,bidx);
  block->map_node(nul_chk, block->end_idx());
  map_node_to_block(nul_chk, block);
  // Redirect users of old_test to nul_chk
  for (DUIterator_Last i2min, i2 = old_tst->last_outs(i2min); i2 >= i2min; --i2)
    old_tst->last_out(i2)->set_req(0, nul_chk);
  // Clean-up any dead code
  for (uint i3 = 0; i3 < old_tst->req(); i3++) {
    Node* in = old_tst->in(i3);
    old_tst->set_req(i3, nullptr);
    if (in->outcnt() == 0) {
      // Remove dead input node
      in->disconnect_inputs(C);
      block->find_remove(in);
    }
  }

  latency_from_uses(nul_chk);
  latency_from_uses(best);

  // insert anti-dependences to defs in this block
  if (! best->needs_anti_dependence_check()) {
    for (uint k = 1; k < block->number_of_nodes(); k++) {
      Node *n = block->get_node(k);
      if (n->needs_anti_dependence_check() &&
          n->in(LoadNode::Memory) == best->in(StoreNode::Memory)) {
        // Found anti-dependent load
        insert_anti_dependences(block, n);
      }
    }
  }
}

//--------------------------catch_cleanup_fix_all_inputs-----------------------
static void catch_cleanup_fix_all_inputs(Node *use, Node *old_def, Node *new_def) {
  for (uint l = 0; l < use->len(); l++) {
    if (use->in(l) == old_def) {
      if (l < use->req()) {
        use->set_req(l, new_def);
      } else {
        use->rm_prec(l);
        use->add_prec(new_def);
        l--;
      }
    }
  }
}

//------------------------------catch_cleanup_find_cloned_def------------------
Node* PhaseCFG::catch_cleanup_find_cloned_def(Block *use_blk, Node *def, Block *def_blk, int n_clone_idx) {
  assert( use_blk != def_blk, "Inter-block cleanup only");

  // The use is some block below the Catch.  Find and return the clone of the def
  // that dominates the use. If there is no clone in a dominating block, then
  // create a phi for the def in a dominating block.

  // Find which successor block dominates this use.  The successor
  // blocks must all be single-entry (from the Catch only; I will have
  // split blocks to make this so), hence they all dominate.
  while( use_blk->_dom_depth > def_blk->_dom_depth+1 )
    use_blk = use_blk->_idom;

  // Find the successor
  Node *fixup = nullptr;

  uint j;
  for( j = 0; j < def_blk->_num_succs; j++ )
    if( use_blk == def_blk->_succs[j] )
      break;

  if( j == def_blk->_num_succs ) {
    // Block at same level in dom-tree is not a successor.  It needs a
    // PhiNode, the PhiNode uses from the def and IT's uses need fixup.
    Node_Array inputs;
    for(uint k = 1; k < use_blk->num_preds(); k++) {
      Block* block = get_block_for_node(use_blk->pred(k));
      inputs.map(k, catch_cleanup_find_cloned_def(block, def, def_blk, n_clone_idx));
    }

    // Check to see if the use_blk already has an identical phi inserted.
    // If it exists, it will be at the first position since all uses of a
    // def are processed together.
    Node *phi = use_blk->get_node(1);
    if( phi->is_Phi() ) {
      fixup = phi;
      for (uint k = 1; k < use_blk->num_preds(); k++) {
        if (phi->in(k) != inputs[k]) {
          // Not a match
          fixup = nullptr;
          break;
        }
      }
    }

    // If an existing PhiNode was not found, make a new one.
    if (fixup == nullptr) {
      Node *new_phi = PhiNode::make(use_blk->head(), def);
      use_blk->insert_node(new_phi, 1);
      map_node_to_block(new_phi, use_blk);
      for (uint k = 1; k < use_blk->num_preds(); k++) {
        new_phi->set_req(k, inputs[k]);
      }
      fixup = new_phi;
    }

  } else {
    // Found the use just below the Catch.  Make it use the clone.
    fixup = use_blk->get_node(n_clone_idx);
  }

  return fixup;
}

//--------------------------catch_cleanup_intra_block--------------------------
// Fix all input edges in use that reference "def".  The use is in the same
// block as the def and both have been cloned in each successor block.
static void catch_cleanup_intra_block(Node *use, Node *def, Block *blk, int beg, int n_clone_idx) {

  // Both the use and def have been cloned. For each successor block,
  // get the clone of the use, and make its input the clone of the def
  // found in that block.

  uint use_idx = blk->find_node(use);
  uint offset_idx = use_idx - beg;
  for( uint k = 0; k < blk->_num_succs; k++ ) {
    // Get clone in each successor block
    Block *sb = blk->_succs[k];
    Node *clone = sb->get_node(offset_idx+1);
    assert( clone->Opcode() == use->Opcode(), "" );

    // Make use-clone reference the def-clone
    catch_cleanup_fix_all_inputs(clone, def, sb->get_node(n_clone_idx));
  }
}

//------------------------------catch_cleanup_inter_block---------------------
// Fix all input edges in use that reference "def".  The use is in a different
// block than the def.
void PhaseCFG::catch_cleanup_inter_block(Node *use, Block *use_blk, Node *def, Block *def_blk, int n_clone_idx) {
  if( !use_blk ) return;        // Can happen if the use is a precedence edge

  Node *new_def = catch_cleanup_find_cloned_def(use_blk, def, def_blk, n_clone_idx);
  catch_cleanup_fix_all_inputs(use, def, new_def);
}

//------------------------------call_catch_cleanup-----------------------------
// If we inserted any instructions between a Call and his CatchNode,
// clone the instructions on all paths below the Catch.
void PhaseCFG::call_catch_cleanup(Block* block) {

  // End of region to clone
  uint end = block->end_idx();
  if( !block->get_node(end)->is_Catch() ) return;
  // Start of region to clone
  uint beg = end;
  while(!block->get_node(beg-1)->is_MachProj() ||
        !block->get_node(beg-1)->in(0)->is_MachCall() ) {
    beg--;
    assert(beg > 0,"Catch cleanup walking beyond block boundary");
  }
  // Range of inserted instructions is [beg, end)
  if( beg == end ) return;

  // Clone along all Catch output paths.  Clone area between the 'beg' and
  // 'end' indices.
  for( uint i = 0; i < block->_num_succs; i++ ) {
    Block *sb = block->_succs[i];
    // Clone the entire area; ignoring the edge fixup for now.
    for( uint j = end; j > beg; j-- ) {
      Node *clone = block->get_node(j-1)->clone();
      sb->insert_node(clone, 1);
      map_node_to_block(clone, sb);
      if (clone->needs_anti_dependence_check()) {
        insert_anti_dependences(sb, clone);
      }
    }
  }


  // Fixup edges.  Check the def-use info per cloned Node
  for(uint i2 = beg; i2 < end; i2++ ) {
    uint n_clone_idx = i2-beg+1; // Index of clone of n in each successor block
    Node *n = block->get_node(i2);        // Node that got cloned
    // Need DU safe iterator because of edge manipulation in calls.
    Unique_Node_List* out = new Unique_Node_List();
    for (DUIterator_Fast j1max, j1 = n->fast_outs(j1max); j1 < j1max; j1++) {
      out->push(n->fast_out(j1));
    }
    uint max = out->size();
    for (uint j = 0; j < max; j++) {// For all users
      Node *use = out->pop();
      Block *buse = get_block_for_node(use);
      if( use->is_Phi() ) {
        for( uint k = 1; k < use->req(); k++ )
          if( use->in(k) == n ) {
            Block* b = get_block_for_node(buse->pred(k));
            Node *fixup = catch_cleanup_find_cloned_def(b, n, block, n_clone_idx);
            use->set_req(k, fixup);
          }
      } else {
        if (block == buse) {
          catch_cleanup_intra_block(use, n, block, beg, n_clone_idx);
        } else {
          catch_cleanup_inter_block(use, buse, n, block, n_clone_idx);
        }
      }
    } // End for all users

  } // End of for all Nodes in cloned area

  // Remove the now-dead cloned ops
  for(uint i3 = beg; i3 < end; i3++ ) {
    block->get_node(beg)->disconnect_inputs(C);
    block->remove_node(beg);
  }

  // If the successor blocks have a CreateEx node, move it back to the top
  for (uint i4 = 0; i4 < block->_num_succs; i4++) {
    Block *sb = block->_succs[i4];
    uint new_cnt = end - beg;
    // Remove any newly created, but dead, nodes by traversing their schedule
    // backwards. Here, a dead node is a node whose only outputs (if any) are
    // unused projections.
    for (uint j = new_cnt; j > 0; j--) {
      Node *n = sb->get_node(j);
      // Individual projections are examined together with all siblings when
      // their parent is visited.
      if (n->is_Proj()) {
        continue;
      }
      bool dead = true;
      for (DUIterator_Fast imax, i = n->fast_outs(imax); i < imax; i++) {
        Node* out = n->fast_out(i);
        // n is live if it has a non-projection output or a used projection.
        if (!out->is_Proj() || out->outcnt() > 0) {
          dead = false;
          break;
        }
      }
      if (dead) {
        // n's only outputs (if any) are unused projections scheduled next to n
        // (see PhaseCFG::select()). Remove these projections backwards.
        for (uint k = j + n->outcnt(); k > j; k--) {
          Node* proj = sb->get_node(k);
          assert(proj->is_Proj() && proj->in(0) == n,
                 "projection should correspond to dead node");
          proj->disconnect_inputs(C);
          sb->remove_node(k);
          new_cnt--;
        }
        // Now remove the node itself.
        n->disconnect_inputs(C);
        sb->remove_node(j);
        new_cnt--;
      }
    }
    // If any newly created nodes remain, move the CreateEx node to the top
    if (new_cnt > 0) {
      Node *cex = sb->get_node(1+new_cnt);
      if( cex->is_Mach() && cex->as_Mach()->ideal_Opcode() == Op_CreateEx ) {
        sb->remove_node(1+new_cnt);
        sb->insert_node(cex, 1);
      }
    }
  }
}
