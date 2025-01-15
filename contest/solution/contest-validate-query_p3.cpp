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
 * Checks the previous block against the block registered in the masterchain.
 * Almost the same as in Collator.
 *
 * @param listed The BlockIdExt of the top block of this shard registered in the masterchain.
 * @param prev The BlockIdExt of the previous block.
 * @param chk_chain_len Flag indicating whether to check the chain length.
 *
 * @returns True if the previous block is valid, false otherwise.
 */
bool ContestValidateQuery::check_prev_block(const BlockIdExt& listed, const BlockIdExt& prev, bool chk_chain_len) {
  if (listed.seqno() > prev.seqno()) {
    return reject_query(PSTRING() << "cannot generate a shardchain block after previous block " << prev.to_str()
                                  << " because masterchain configuration already contains a newer block "
                                  << listed.to_str());
  }
  if (listed.seqno() == prev.seqno() && listed != prev) {
    return reject_query(PSTRING() << "cannot generate a shardchain block after previous block " << prev.to_str()
                                  << " because masterchain configuration lists another block " << listed.to_str()
                                  << " of the same height");
  }
  if (chk_chain_len && prev.seqno() >= listed.seqno() + 8) {
    return reject_query(PSTRING() << "cannot generate next block after " << prev.to_str()
                                  << " because this would lead to an unregistered chain of length > 8 (only "
                                  << listed.to_str() << " is registered in the masterchain)");
  }
  return true;
}

/**
 * Checks the previous block against the block registered in the masterchain.
 * Almost the same as in Collator
 *
 * @param listed The BlockIdExt of the top block of this shard registered in the masterchain.
 * @param prev The BlockIdExt of the previous block.
 *
 * @returns True if the previous block is equal to the one registered in the masterchain, false otherwise.
 */
bool ContestValidateQuery::check_prev_block_exact(const BlockIdExt& listed, const BlockIdExt& prev) {
  if (listed != prev) {
    return reject_query(PSTRING() << "cannot generate shardchain block for shard " << shard_.to_str()
                                  << " after previous block " << prev.to_str()
                                  << " because masterchain configuration expects another previous block "
                                  << listed.to_str() << " and we are immediately after a split/merge event");
  }
  return true;
}

/**
 * Checks the validity of the shard configuration of the current shard.
 * Almost the same as in Collator (main change: fatal_error -> reject_query).
 *
 * @returns True if the shard's configuration is valid, False otherwise.
 */
bool ContestValidateQuery::check_this_shard_mc_info() {
  wc_info_ = config_->get_workchain_info(workchain());
  if (wc_info_.is_null()) {
    return reject_query(PSTRING() << "cannot create new block for workchain " << workchain()
                                  << " absent from workchain configuration");
  }
  if (!wc_info_->active) {
    return reject_query(PSTRING() << "cannot create new block for disabled workchain " << workchain());
  }
  if (!wc_info_->basic) {
    return reject_query(PSTRING() << "cannot create new block for non-basic workchain " << workchain());
  }
  if (wc_info_->enabled_since && wc_info_->enabled_since > config_->utime) {
    return reject_query(PSTRING() << "cannot create new block for workchain " << workchain()
                                  << " which is not enabled yet");
  }
  if (wc_info_->min_addr_len != 0x100 || wc_info_->max_addr_len != 0x100) {
    return false;
  }
  accept_msgs_ = wc_info_->accept_msgs;
  bool split_allowed = false;
  if (!config_->has_workchain(workchain())) {
    // creating first block for a new workchain
    LOG(INFO) << "creating first block for workchain " << workchain();
    return reject_query(PSTRING() << "cannot create first block for workchain " << workchain()
                                  << " after previous block "
                                  << (prev_blocks.size() ? prev_blocks[0].to_str() : "(null)")
                                  << " because no shard for this workchain is declared yet");
  }
  auto left = config_->get_shard_hash(shard_ - 1, false);
  if (left.is_null()) {
    return reject_query(PSTRING() << "cannot create new block for shard " << shard_.to_str()
                                  << " because there is no similar shard in existing masterchain configuration");
  }
  if (left->shard() == shard_) {
    // no split/merge
    if (after_merge_ || after_split_) {
      return reject_query(
          PSTRING() << "cannot generate new shardchain block for " << shard_.to_str()
                    << " after a supposed split or merge event because this event is not reflected in the masterchain");
    }
    if (!check_prev_block(left->blk_, prev_blocks[0])) {
      return false;
    }
    if (left->before_split_) {
      return reject_query(PSTRING() << "cannot generate new unsplit shardchain block for " << shard_.to_str()
                                    << " after previous block " << left->blk_.to_str() << " with before_split set");
    }
    auto sib = config_->get_shard_hash(shard_sibling(shard_));
    if (left->before_merge_ && sib->before_merge_) {
      return reject_query(PSTRING() << "cannot generate new unmerged shardchain block for " << shard_.to_str()
                                    << " after both " << left->blk_.to_str() << " and " << sib->blk_.to_str()
                                    << " set before_merge flags");
    }
    if (left->is_fsm_split()) {
      if (now_ >= left->fsm_utime() && now_ < left->fsm_utime_end()) {
        split_allowed = true;
      }
    }
  } else if (shard_is_parent(shard_, left->shard())) {
    // after merge
    if (!left->before_merge_) {
      return reject_query(PSTRING() << "cannot create new merged block for shard " << shard_.to_str()
                                    << " because its left ancestor " << left->blk_.to_str()
                                    << " has no before_merge flag");
    }
    auto right = config_->get_shard_hash(shard_ + 1, false);
    if (right.is_null()) {
      return reject_query(
          PSTRING()
          << "cannot create new block for shard " << shard_.to_str()
          << " after a preceding merge because there is no right ancestor shard in existing masterchain configuration");
    }
    if (!shard_is_parent(shard_, right->shard())) {
      return reject_query(PSTRING() << "cannot create new block for shard " << shard_.to_str()
                                    << " after a preceding merge because its right ancestor appears to be "
                                    << right->blk_.to_str());
    }
    if (!right->before_merge_) {
      return reject_query(PSTRING() << "cannot create new merged block for shard " << shard_.to_str()
                                    << " because its right ancestor " << right->blk_.to_str()
                                    << " has no before_merge flag");
    }
    if (after_split_) {
      return reject_query(
          PSTRING() << "cannot create new block for shard " << shard_.to_str()
                    << " after a purported split because existing shard configuration suggests a merge");
    } else if (after_merge_) {
      if (!(check_prev_block_exact(left->blk_, prev_blocks[0]) &&
            check_prev_block_exact(right->blk_, prev_blocks[1]))) {
        return false;
      }
    } else {
      auto cseqno = std::max(left->seqno(), right->seqno());
      if (prev_blocks[0].seqno() <= cseqno) {
        return reject_query(PSTRING() << "cannot create new block for shard " << shard_.to_str()
                                      << " after previous block " << prev_blocks[0].to_str()
                                      << " because masterchain contains newer possible ancestors "
                                      << left->blk_.to_str() << " and " << right->blk_.to_str());
      }
      if (prev_blocks[0].seqno() >= cseqno + 8) {
        return reject_query(
            PSTRING() << "cannot create new block for shard " << shard_.to_str() << " after previous block "
                      << prev_blocks[0].to_str()
                      << " because this would lead to an unregistered chain of length > 8 (masterchain contains only "
                      << left->blk_.to_str() << " and " << right->blk_.to_str() << ")");
      }
    }
  } else if (shard_is_parent(left->shard(), shard_)) {
    // after split
    if (!left->before_split_) {
      return reject_query(PSTRING() << "cannot generate new split shardchain block for " << shard_.to_str()
                                    << " after previous block " << left->blk_.to_str() << " without before_split");
    }
    if (after_merge_) {
      return reject_query(
          PSTRING() << "cannot create new block for shard " << shard_.to_str()
                    << " after a purported merge because existing shard configuration suggests a split");
    } else if (after_split_) {
      if (!(check_prev_block_exact(left->blk_, prev_blocks[0]))) {
        return false;
      }
    } else {
      if (!(check_prev_block(left->blk_, prev_blocks[0]))) {
        return false;
      }
    }
  } else {
    return reject_query(PSTRING() << "masterchain configuration contains only block " << left->blk_.to_str()
                                  << " which belongs to a different shard from ours " << shard_.to_str());
  }
  if (before_split_ && !split_allowed) {
    return reject_query(PSTRING() << "new block " << id_.to_str()
                                  << " has before_split set, but this is forbidden by masterchain configuration");
  }
  return true;
}

/*
 *
 *  METHODS CALLED FROM try_validate() stage 0
 *
 */

/**
 * Computes the previous shard state.
 *
 * @returns True if the previous state is computed successfully, false otherwise.
 */
bool ContestValidateQuery::compute_prev_state() {
  CHECK(prev_states.size() == 1u + after_merge_);

  prev_state_root_ = prev_states[0]->root_cell();
  CHECK(prev_state_root_.not_null());
  if (after_merge_) {
    Ref<vm::Cell> aux_root = prev_states[1]->root_cell();
    if (!block::gen::t_ShardState.cell_pack_split_state(prev_state_root_, prev_states[0]->root_cell(),
                                                        prev_states[1]->root_cell())) {
      return fatal_error(-667, "cannot construct mechanically merged previously state");
    }
  }
  state_usage_tree_ = std::make_shared<vm::CellUsageTree>();
  prev_state_root_ = vm::UsageCell::create(prev_state_root_, state_usage_tree_->root_ptr());
  return true;
}

/**
 * Unpacks and merges the states of two previous blocks.
 * Used if the block is after_merge.
 * Similar to Collator::unpack_merge_last_state()
 *
 * @returns True if the unpacking and merging was successful, false otherwise.
 */
bool ContestValidateQuery::unpack_merge_prev_state() {
  LOG(DEBUG) << "unpack/merge previous states";
  CHECK(prev_states.size() == 2);
  // 2. extract the two previous states
  Ref<vm::Cell> root0, root1;
  if (!block::gen::t_ShardState.cell_unpack_split_state(prev_state_root_, root0, root1)) {
    return fatal_error(-667, "cannot unsplit a virtual split_state after a merge");
  }
  // 3. unpack previous states
  // 3.1. unpack left ancestor
  if (!unpack_one_prev_state(ps_, prev_blocks.at(0), std::move(root0))) {
    return fatal_error("cannot unpack the state of left ancestor "s + prev_blocks.at(0).to_str());
  }
  // 3.2. unpack right ancestor
  block::ShardState ss1;
  if (!unpack_one_prev_state(ss1, prev_blocks.at(1), std::move(root1))) {
    return fatal_error("cannot unpack the state of right ancestor "s + prev_blocks.at(1).to_str());
  }
  // 4. merge the two ancestors of the current state
  LOG(INFO) << "merging the two previous states";
  auto res = ps_.merge_with(ss1);
  if (res.is_error()) {
    return fatal_error(std::move(res)) || fatal_error("cannot merge the two previous states");
  }
  return true;
}

/**
 * Unpacks the state of the previous block.
 * Used if the block is not after_merge.
 * Similar to Collator::unpack_last_state()
 *
 * @returns True if the unpacking is successful, false otherwise.
 */
bool ContestValidateQuery::unpack_prev_state() {
  LOG(DEBUG) << "unpacking previous state(s)";
  CHECK(prev_state_root_.not_null());
  if (after_merge_) {
    if (!unpack_merge_prev_state()) {
      return fatal_error("unable to unpack/merge previous states immediately after a merge");
    }
    return true;
  }
  CHECK(prev_states.size() == 1);
  // unpack previous state
  return unpack_one_prev_state(ps_, prev_blocks.at(0), prev_state_root_) && (!after_split_ || split_prev_state(ps_));
}

/**
 * Unpacks the state of a previous block and performs necessary checks.
 * Similar to Collator::unpack_one_last_state()
 *
 * @param ss The ShardState object to unpack the state into.
 * @param blkid The BlockIdExt of the previous block.
 * @param prev_state_root The root of the state.
 *
 * @returns True if the unpacking and checks are successful, false otherwise.
 */
bool ContestValidateQuery::unpack_one_prev_state(block::ShardState& ss, BlockIdExt blkid,
                                                 Ref<vm::Cell> prev_state_root) {
  auto res = ss.unpack_state_ext(blkid, std::move(prev_state_root), global_id_, mc_seqno_, after_split_,
                                 after_split_ | after_merge_, [this](ton::BlockSeqno mc_seqno) {
                                   Ref<MasterchainStateQ> state;
                                   return request_aux_mc_state(mc_seqno, state);
                                 });
  if (res.is_error()) {
    return fatal_error(std::move(res));
  }
  if (ss.vert_seqno_ > vert_seqno_) {
    return reject_query(PSTRING() << "one of previous states " << ss.id_.to_str() << " has vertical seqno "
                                  << ss.vert_seqno_ << " larger than that of the new block " << vert_seqno_);
  }
  return true;
}

/**
 * Splits the state of previous block.
 * Used if the block is after_split.
 * Similar to Collator::split_last_state()
 *
 * @param ss The ShardState object representing the previous state. The result is stored here.
 *
 * @returns True if the split operation is successful, false otherwise.
 */
bool ContestValidateQuery::split_prev_state(block::ShardState& ss) {
  LOG(INFO) << "Splitting previous state " << ss.id_.to_str() << " to subshard " << shard_.to_str();
  CHECK(after_split_);
  auto sib_shard = ton::shard_sibling(shard_);
  auto res1 = ss.compute_split_out_msg_queue(sib_shard);
  if (res1.is_error()) {
    return fatal_error(res1.move_as_error());
  }
  sibling_out_msg_queue_ = res1.move_as_ok();
  auto res2 = ss.compute_split_processed_upto(sib_shard);
  if (res2.is_error()) {
    return fatal_error(res2.move_as_error());
  }
  sibling_processed_upto_ = res2.move_as_ok();
  auto res3 = ss.split(shard_);
  if (res3.is_error()) {
    return fatal_error(std::move(res3));
  }
  return true;
}

}  // namespace solution
