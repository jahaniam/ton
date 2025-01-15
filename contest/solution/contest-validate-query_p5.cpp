#include "contest-validate-query.hpp"
#include "top-shard-descr.hpp"
#include "validator-set.hpp"
#include "adnl/utils.hpp"
#include "ton/ton-tl.hpp"
#include "ton/ton-io.hpp"
#include "vm/boc.h"
#include "block/block-db.h"
#include "block/block.h"
#include "block/block-parse.h"
#include "block/block-auto.h"
#include "block/output-queue-merger.h"
#include "vm/cells/MerkleProof.h"
#include "vm/cells/MerkleUpdate.h"
#include "common/errorlog.h"
#include "fabric.h"
#include <ctime>

namespace solution {

using namespace ton;
using namespace ton::validator;

using td::Ref;
using namespace std::literals::string_literals;


/**
 * Handles the result of obtaining the size of the outbound message queue.
 *
 * If the block is after merge then the two sizes are added.
 *
 * @param i The index of the previous block (0 or 1).
 * @param res The result object containing the size of the queue.
 */
void ContestValidateQuery::got_out_queue_size(size_t i, td::Result<td::uint64> res) {
  --pending;
  if (res.is_error()) {
    fatal_error(
        res.move_as_error_prefix(PSTRING() << "failed to get message queue size from prev block #" << i << ": "));
    return;
  }
  td::uint64 size = res.move_as_ok();
  LOG(DEBUG) << "got outbound queue size from prev block #" << i << ": " << size;
  old_out_msg_queue_size_ += size;
  try_validate();
}

/*
 *
 *  METHODS CALLED FROM try_validate() stage 1
 *
 */

/**
 * Adjusts one entry from the processed up to information using the masterchain state that is referenced in the entry.
 * Almost the same as in Collator (but it can take into account the new state of the masterchain).
 *
 * @param proc The MsgProcessedUpto object.
 * @param owner The shard that the MsgProcessesUpto information is taken from.
 * @param allow_cur Allow using the new state of the msaterchain.
 *
 * @returns True if the processed up to information was successfully adjusted, false otherwise.
 */
bool ContestValidateQuery::fix_one_processed_upto(block::MsgProcessedUpto& proc, ton::ShardIdFull owner,
                                                  bool allow_cur) {
  if (proc.compute_shard_end_lt) {
    return true;
  }
  auto seqno = std::min(proc.mc_seqno, mc_seqno_);
  {
    auto state = get_aux_mc_state(seqno);
    if (state.is_null()) {
      return fatal_error(
          -666, PSTRING() << "cannot obtain masterchain state with seqno " << seqno << " (originally required "
                          << proc.mc_seqno << ") in a MsgProcessedUpto record for "
                          << ton::ShardIdFull{owner.workchain, proc.shard}.to_str() << " owned by " << owner.to_str());
    }
    proc.compute_shard_end_lt = state->get_config()->get_compute_shard_end_lt_func();
  }
  return (bool)proc.compute_shard_end_lt;
}

/**
 * Adjusts the processed up to collection using the using the auxilliary masterchain states.
 * Almost the same as in Collator.
 *
 * @param upto The MsgProcessedUptoCollection to be adjusted.
 * @param allow_cur Allow using the new state of the msaterchain.
 *
 * @returns True if all entries were successfully adjusted, False otherwise.
 */
bool ContestValidateQuery::fix_processed_upto(block::MsgProcessedUptoCollection& upto, bool allow_cur) {
  for (auto& entry : upto.list) {
    if (!fix_one_processed_upto(entry, upto.owner, allow_cur)) {
      return false;
    }
  }
  return true;
}

/**
 * Adjusts the processed_upto values for all shard states, including neighbors.
 *
 * @returns True if all processed_upto values were successfully adjusted, false otherwise.
 */
bool ContestValidateQuery::fix_all_processed_upto() {
  CHECK(ps_.processed_upto_);
  if (!fix_processed_upto(*ps_.processed_upto_)) {
    return fatal_error("Cannot adjust old ProcessedUpto of our shard state");
  }
  if (sibling_processed_upto_ && !fix_processed_upto(*sibling_processed_upto_)) {
    return fatal_error("Cannot adjust old ProcessedUpto of the shard state of our virtual sibling");
  }
  if (!fix_processed_upto(*ns_.processed_upto_, true)) {
    return fatal_error("Cannot adjust new ProcessedUpto of our shard state");
  }
  for (auto& descr : neighbors_) {
    CHECK(descr.processed_upto);
    if (!fix_processed_upto(*descr.processed_upto)) {
      return fatal_error("Cannot adjust ProcessedUpto of neighbor "s + descr.blk_.to_str());
    }
  }
  return true;
}

/**
 * Adds trivials neighbor after merging two shards.
 * Trivial neighbors are the two previous blocks.
 * Almost the same as in Collator.
 *
 * @returns True if the operation is successful, false otherwise.
 */
bool ContestValidateQuery::add_trivial_neighbor_after_merge() {
  LOG(DEBUG) << "in add_trivial_neighbor_after_merge()";
  CHECK(prev_blocks.size() == 2);
  int found = 0;
  std::size_t n = neighbors_.size();
  for (std::size_t i = 0; i < n; i++) {
    auto& nb = neighbors_.at(i);
    if (ton::shard_intersects(nb.shard(), shard_)) {
      ++found;
      LOG(DEBUG) << "neighbor #" << i << " : " << nb.blk_.to_str() << " intersects our shard " << shard_.to_str();
      if (!ton::shard_is_parent(shard_, nb.shard()) || found > 2) {
        return fatal_error("impossible shard configuration in add_trivial_neighbor_after_merge()");
      }
      auto prev_shard = prev_blocks.at(found - 1).shard_full();
      if (nb.shard() != prev_shard) {
        return fatal_error("neighbor shard "s + nb.shard().to_str() + " does not match that of our ancestor " +
                           prev_shard.to_str());
      }
      if (found == 1) {
        nb.set_queue_root(ps_.out_msg_queue_->get_root_cell());
        nb.processed_upto = ps_.processed_upto_;
        nb.blk_.id.shard = shard_.shard;
        LOG(DEBUG) << "adjusted neighbor #" << i << " : " << nb.blk_.to_str()
                   << " with shard expansion (immediate after-merge adjustment)";
      } else {
        LOG(DEBUG) << "disabling neighbor #" << i << " : " << nb.blk_.to_str() << " (immediate after-merge adjustment)";
        nb.disable();
      }
    }
  }
  CHECK(found == 2);
  return true;
}

/**
 * Adds a trivial neighbor.
 * A trivial neighbor is the previous block.
 * Almost the same as in Collator.
 *
 * @returns True if the operation is successful, false otherwise.
 */
bool ContestValidateQuery::add_trivial_neighbor() {
  LOG(DEBUG) << "in add_trivial_neighbor()";
  if (after_merge_) {
    return add_trivial_neighbor_after_merge();
  }
  CHECK(prev_blocks.size() == 1);
  if (!prev_blocks[0].seqno()) {
    // skipping
    LOG(DEBUG) << "no trivial neighbor because previous block has zero seqno";
    return true;
  }
  CHECK(prev_state_root_.not_null());
  auto descr_ref = block::McShardDescr::from_state(prev_blocks[0], prev_state_root_);
  if (descr_ref.is_null()) {
    return reject_query("cannot deserialize header of previous state");
  }
  CHECK(descr_ref.not_null());
  CHECK(descr_ref->blk_ == prev_blocks[0]);
  CHECK(ps_.out_msg_queue_);
  ton::ShardIdFull prev_shard = descr_ref->shard();
  // Possible cases are:
  // 1. prev_shard = shard = one of neighbors
  //    => replace neighbor by (more recent) prev_shard info
  // 2. shard is child of prev_shard = one of neighbors
  //    => after_split must be set;
  //       replace neighbor by new split data (and shrink its shard);
  //       insert new virtual neighbor (our future sibling).
  // 3. prev_shard = shard = child of one of neighbors
  //    => after_split must be clear (we are continuing an after-split chain);
  //       make our virtual sibling from the neighbor (split its queue);
  //       insert ourselves from prev_shard data
  // In all of the above cases, our shard intersects exactly one neighbor, which has the same shard or its parent.
  // 4. there are two neighbors intersecting shard = prev_shard, which are its children.
  // 5. there are two prev_shards, the two children of shard, and two neighbors coinciding with prev_shards
  int found = 0, cs = 0;
  std::size_t n = neighbors_.size();
  for (std::size_t i = 0; i < n; i++) {
    auto& nb = neighbors_.at(i);
    if (ton::shard_intersects(nb.shard(), shard_)) {
      ++found;
      LOG(DEBUG) << "neighbor #" << i << " : " << nb.blk_.to_str() << " intersects our shard " << shard_.to_str();
      if (nb.shard() == prev_shard) {
        if (prev_shard == shard_) {
          // case 1. Normal.
          CHECK(found == 1);
          nb = *descr_ref;
          nb.set_queue_root(ps_.out_msg_queue_->get_root_cell());
          nb.processed_upto = ps_.processed_upto_;
          LOG(DEBUG) << "adjusted neighbor #" << i << " : " << nb.blk_.to_str() << " (simple replacement)";
          cs = 1;
        } else if (ton::shard_is_parent(nb.shard(), shard_)) {
          // case 2. Immediate after-split.
          CHECK(found == 1);
          CHECK(after_split_);
          CHECK(sibling_out_msg_queue_);
          CHECK(sibling_processed_upto_);
          neighbors_.emplace_back(*descr_ref);
          auto& nb2 = neighbors_.at(i);
          nb2.set_queue_root(sibling_out_msg_queue_->get_root_cell());
          nb2.processed_upto = sibling_processed_upto_;
          nb2.blk_.id.shard = ton::shard_sibling(shard_.shard);
          LOG(DEBUG) << "adjusted neighbor #" << i << " : " << nb2.blk_.to_str()
                     << " with shard shrinking to our sibling (immediate after-split adjustment)";
          auto& nb1 = neighbors_.at(n);
          nb1.set_queue_root(ps_.out_msg_queue_->get_root_cell());
          nb1.processed_upto = ps_.processed_upto_;
          nb1.blk_.id.shard = shard_.shard;
          LOG(DEBUG) << "created neighbor #" << n << " : " << nb1.blk_.to_str()
                     << " with shard shrinking to our (immediate after-split adjustment)";
          cs = 2;
        } else {
          return fatal_error("impossible shard configuration in add_trivial_neighbor()");
        }
      } else if (ton::shard_is_parent(nb.shard(), shard_) && shard_ == prev_shard) {
        // case 3. Continued after-split
        CHECK(found == 1);
        CHECK(!after_split_);
        CHECK(!sibling_out_msg_queue_);
        CHECK(!sibling_processed_upto_);
        neighbors_.emplace_back(*descr_ref);
        auto& nb2 = neighbors_.at(i);
        auto sib_shard = ton::shard_sibling(shard_);
        // compute the part of virtual sibling's OutMsgQueue with destinations in our shard
        sibling_out_msg_queue_ =
            std::make_unique<vm::AugmentedDictionary>(nb2.outmsg_root, 352, block::tlb::aug_OutMsgQueue);
        td::BitArray<96> pfx;
        pfx.bits().store_int(shard_.workchain, 32);
        (pfx.bits() + 32).store_uint(shard_.shard, 64);
        int l = ton::shard_prefix_length(shard_);
        CHECK(sibling_out_msg_queue_->cut_prefix_subdict(pfx.bits(), 32 + l));
        int res2 = block::filter_out_msg_queue(*sibling_out_msg_queue_, nb2.shard(), sib_shard);
        if (res2 < 0) {
          return fatal_error("cannot filter virtual sibling's OutMsgQueue from that of the last common ancestor");
        }
        nb2.set_queue_root(sibling_out_msg_queue_->get_root_cell());
        if (!nb2.processed_upto->split(sib_shard)) {
          return fatal_error("error splitting ProcessedUpto for our virtual sibling");
        }
        nb2.blk_.id.shard = ton::shard_sibling(shard_.shard);
        LOG(DEBUG) << "adjusted neighbor #" << i << " : " << nb2.blk_.to_str()
                   << " with shard shrinking to our sibling (continued after-split adjustment)";
        auto& nb1 = neighbors_.at(n);
        nb1.set_queue_root(ps_.out_msg_queue_->get_root_cell());
        nb1.processed_upto = ps_.processed_upto_;
        LOG(DEBUG) << "created neighbor #" << n << " : " << nb1.blk_.to_str()
                   << " from our preceding state (continued after-split adjustment)";
        cs = 3;
      } else if (ton::shard_is_parent(shard_, nb.shard()) && shard_ == prev_shard) {
        // case 4. Continued after-merge.
        if (found == 1) {
          cs = 4;
        }
        CHECK(cs == 4);
        CHECK(found <= 2);
        if (found == 1) {
          nb = *descr_ref;
          nb.set_queue_root(ps_.out_msg_queue_->get_root_cell());
          nb.processed_upto = ps_.processed_upto_;
          LOG(DEBUG) << "adjusted neighbor #" << i << " : " << nb.blk_.to_str()
                     << " with shard expansion (continued after-merge adjustment)";
        } else {
          LOG(DEBUG) << "disabling neighbor #" << i << " : " << nb.blk_.to_str()
                     << " (continued after-merge adjustment)";
          nb.disable();
        }
      } else {
        return fatal_error("impossible shard configuration in add_trivial_neighbor()");
      }
    }
  }
  CHECK(found && cs);
  CHECK(found == (1 + (cs == 4)));
  return true;
}

/**
 * Unpacks block data and performs validation checks.
 *
 * @returns True if the block data is successfully unpacked and passes all validation checks, false otherwise.
 */
bool ContestValidateQuery::unpack_block_data() {
  LOG(DEBUG) << "unpacking block structures";
  block::gen::Block::Record blk;
  block::gen::BlockExtra::Record extra;
  if (!(tlb::unpack_cell(block_root_, blk) && tlb::unpack_cell(blk.extra, extra))) {
    return reject_query("cannot unpack Block header");
  }
  auto inmsg_cs = vm::load_cell_slice_ref(std::move(extra.in_msg_descr));
  auto outmsg_cs = vm::load_cell_slice_ref(std::move(extra.out_msg_descr));
  // run some hand-written checks from block::tlb::
  // (automatic tests from block::gen:: have been already run for the entire block)
  if (!block::tlb::t_InMsgDescr.validate_upto(10000000, *inmsg_cs)) {
    return reject_query("InMsgDescr of the new block failed to pass handwritten validity tests");
  }
  if (!block::tlb::t_OutMsgDescr.validate_upto(10000000, *outmsg_cs)) {
    return reject_query("OutMsgDescr of the new block failed to pass handwritten validity tests");
  }
  if (!block::tlb::t_ShardAccountBlocks.validate_ref(10000000, extra.account_blocks)) {
    return reject_query("ShardAccountBlocks of the new block failed to pass handwritten validity tests");
  }
  in_msg_dict_ = std::make_unique<vm::AugmentedDictionary>(std::move(inmsg_cs), 256, block::tlb::aug_InMsgDescr);
  out_msg_dict_ = std::make_unique<vm::AugmentedDictionary>(std::move(outmsg_cs), 256, block::tlb::aug_OutMsgDescr);
  account_blocks_dict_ = std::make_unique<vm::AugmentedDictionary>(
      vm::load_cell_slice_ref(std::move(extra.account_blocks)), 256, block::tlb::aug_ShardAccountBlocks);
  LOG(DEBUG) << "validating InMsgDescr";
  if (!in_msg_dict_->validate_all()) {
    return reject_query("InMsgDescr dictionary is invalid");
  }
  LOG(DEBUG) << "validating OutMsgDescr";
  if (!out_msg_dict_->validate_all()) {
    return reject_query("OutMsgDescr dictionary is invalid");
  }
  LOG(DEBUG) << "validating ShardAccountBlocks";
  if (!account_blocks_dict_->validate_all()) {
    return reject_query("ShardAccountBlocks dictionary is invalid");
  }
  return unpack_precheck_value_flow(std::move(blk.value_flow));
}


}  // namespace solution
