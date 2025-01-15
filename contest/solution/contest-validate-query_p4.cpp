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


bool ContestValidateQuery::init_next_state() {
  ns_.id_ = id_;
  ns_.global_id_ = global_id_;
  ns_.utime_ = now_;
  ns_.lt_ = end_lt_;
  ns_.mc_blk_ref_ = mc_blkid_;
  ns_.vert_seqno_ = vert_seqno_;
  ns_.before_split_ = before_split_;
  ns_.processed_upto_ = block::MsgProcessedUptoCollection::unpack(id_.shard_full(), extra_collated_data_.proc_info);
  if (!ns_.processed_upto_) {
    return reject_query("failed top unpack processed upto");
  }
  return true;
}

/**
 * Requests the message queues of neighboring shards.
 * Almost the same as in Collator.
 *
 * @returns True if the request for neighbor message queues was successful, false otherwise.
 */
bool ContestValidateQuery::request_neighbor_queues() {
  CHECK(new_shard_conf_);
  auto neighbor_list = new_shard_conf_->get_neighbor_shard_hash_ids(shard_);
  LOG(DEBUG) << "got a preliminary list of " << neighbor_list.size() << " neighbors for " << shard_.to_str();
  for (ton::BlockId blk_id : neighbor_list) {
    if (blk_id.seqno == 0 && blk_id.shard_full() != shard_) {
      continue;
    }
    auto shard_ptr = new_shard_conf_->get_shard_hash(ton::ShardIdFull(blk_id));
    if (shard_ptr.is_null()) {
      return reject_query("cannot obtain shard hash for neighbor "s + blk_id.to_str());
    }
    if (shard_ptr->blk_.id != blk_id) {
      return reject_query("invalid block id "s + shard_ptr->blk_.to_str() + " returned in information for neighbor " +
                          blk_id.to_str());
    }
    neighbors_.emplace_back(*shard_ptr);
  }
  int i = 0;
  {
    for (block::McShardDescr& descr : neighbors_) {
      LOG(DEBUG) << "requesting outbound queue of neighbor #" << i << " : " << descr.blk_.to_str();
      ++pending;
      auto r_state = fetch_block_state(descr.blk_);
      if (r_state.is_error()) {
        return fatal_error(r_state.move_as_error());
      }
      td::actor::send_closure(actor_id(this), &ContestValidateQuery::got_neighbor_out_queue, i,
                              r_state.ok()->message_queue());
      ++i;
    }
  }
  return true;
}

/**
 * Handles the result of obtaining the outbound queue for a neighbor.
 * Almost the same as in Collator.
 *
 * @param i The index of the neighbor.
 * @param res The obtained outbound queue.
 */
void ContestValidateQuery::got_neighbor_out_queue(int i, td::Result<Ref<MessageQueue>> res) {
  --pending;
  if (res.is_error()) {
    fatal_error(res.move_as_error());
    return;
  }
  Ref<MessageQueue> outq_descr = res.move_as_ok();
  block::McShardDescr& descr = neighbors_.at(i);
  LOG(INFO) << "obtained outbound queue for neighbor #" << i << " : " << descr.shard().to_str();
  if (outq_descr->get_block_id() != descr.blk_) {
    LOG(DEBUG) << "outq_descr->id = " << outq_descr->get_block_id().to_str() << " ; descr.id = " << descr.blk_.to_str();
    fatal_error(
        -667, "invalid outbound queue information returned for "s + descr.shard().to_str() + " : id or hash mismatch");
    return;
  }
  if (outq_descr->root_cell().is_null()) {
    fatal_error("no OutMsgQueueInfo in queue info in a neighbor state");
    return;
  }
  block::gen::OutMsgQueueInfo::Record qinfo;
  if (!tlb::unpack_cell(outq_descr->root_cell(), qinfo)) {
    fatal_error("cannot unpack neighbor output queue info");
    return;
  }
  descr.set_queue_root(qinfo.out_queue->prefetch_ref(0));
  // TODO: comment the next two lines in the future when the output queues become huge
  // (do this carefully)
  if (debug_checks_) {
    CHECK(block::gen::t_OutMsgQueueInfo.validate_ref(1000000, outq_descr->root_cell()));
    CHECK(block::tlb::t_OutMsgQueueInfo.validate_ref(1000000, outq_descr->root_cell()));
  }
  // unpack ProcessedUpto
  LOG(DEBUG) << "unpacking ProcessedUpto of neighbor " << descr.blk_.to_str();
  if (verbosity >= 2) {
    block::gen::t_ProcessedInfo.print(std::cerr, qinfo.proc_info);
    qinfo.proc_info->print_rec(std::cerr);
  }
  descr.processed_upto = block::MsgProcessedUptoCollection::unpack(descr.shard(), qinfo.proc_info);
  if (!descr.processed_upto) {
    fatal_error("cannot unpack ProcessedUpto in neighbor output queue info for neighbor "s + descr.blk_.to_str());
    return;
  }
  outq_descr.clear();
  do {
    // require masterchain blocks referred to in ProcessedUpto
    // TODO: perform this only if there are messages for this shard in our output queue
    // .. (have to check the above condition and perform a `break` here) ..
    // ..
    for (const auto& entry : descr.processed_upto->list) {
      Ref<MasterchainStateQ> state;
      if (!request_aux_mc_state(entry.mc_seqno, state)) {
        return;
      }
    }
  } while (false);
  if (!pending) {
    LOG(INFO) << "all neighbor output queues fetched";
    try_validate();
  }
}

/**
 * Registers a masterchain state.
 * Almost the same as in Collator.
 *
 * @param other_mc_state The masterchain state to register.
 *
 * @returns True if the registration is successful, false otherwise.
 */
bool ContestValidateQuery::register_mc_state(Ref<MasterchainStateQ> other_mc_state) {
  if (other_mc_state.is_null() || mc_state_.is_null()) {
    return false;
  }
  if (!mc_state_->check_old_mc_block_id(other_mc_state->get_block_id())) {
    return fatal_error(
        "attempting to register masterchain state for block "s + other_mc_state->get_block_id().to_str() +
        " which is not an ancestor of most recent masterchain block " + mc_state_->get_block_id().to_str());
  }
  auto seqno = other_mc_state->get_seqno();
  auto res = aux_mc_states_.insert(std::make_pair(seqno, other_mc_state));
  if (res.second) {
    return true;  // inserted
  }
  auto& found = res.first->second;
  if (found.is_null()) {
    found = std::move(other_mc_state);
    return true;
  } else if (found->get_block_id() != other_mc_state->get_block_id()) {
    return fatal_error("got two masterchain states of same height corresponding to different blocks "s +
                       found->get_block_id().to_str() + " and " + other_mc_state->get_block_id().to_str());
  }
  return true;
}

/**
 * Requests the auxiliary masterchain state.
 * Almost the same as in Collator
 *
 * @param seqno The seqno of the block.
 * @param state A reference to the auxiliary masterchain state.
 *
 * @returns True if the auxiliary masterchain state is successfully requested, false otherwise.
 */
bool ContestValidateQuery::request_aux_mc_state(BlockSeqno seqno, Ref<MasterchainStateQ>& state) {
  if (mc_state_.is_null()) {
    return fatal_error(PSTRING() << "cannot find masterchain block with seqno " << seqno
                                 << " to load corresponding state because no masterchain state is known yet");
  }
  if (seqno > mc_state_->get_seqno()) {
    state = mc_state_;
    return true;
  }
  auto res = aux_mc_states_.insert(std::make_pair(seqno, Ref<MasterchainStateQ>{}));
  if (!res.second) {
    state = res.first->second;
    return true;
  }
  BlockIdExt blkid;
  if (!mc_state_->get_old_mc_block_id(seqno, blkid)) {
    return fatal_error(PSTRING() << "cannot find masterchain block with seqno " << seqno
                                 << " to load corresponding state as required");
  }
  CHECK(blkid.is_valid_ext() && blkid.is_masterchain());
  LOG(DEBUG) << "sending auxiliary wait_block_state() query for " << blkid.to_str() << " to Manager";
  ++pending;
  td::actor::send_closure_later(actor_id(this), &ContestValidateQuery::after_get_aux_shard_state, blkid,
                                fetch_block_state(blkid));
  state.clear();
  return true;
}

/**
 * Retrieves the auxiliary masterchain state for a given block sequence number.
 * Almost the same as in Collator.
 *
 * @param seqno The sequence number of the block.
 *
 * @returns A reference to the auxiliary masterchain state if found, otherwise an empty reference.
 */
Ref<MasterchainStateQ> ContestValidateQuery::get_aux_mc_state(BlockSeqno seqno) const {
  auto it = aux_mc_states_.find(seqno);
  if (it != aux_mc_states_.end()) {
    return it->second;
  } else {
    return {};
  }
}

/**
 * Callback function called after retrieving the auxiliary shard state.
 * Handles the retrieved shard state and performs necessary checks and registrations.
 * Almost the same as in Collator.
 *
 * @param blkid The BlockIdExt of the shard state.
 * @param res The result of retrieving the shard state.
 */
void ContestValidateQuery::after_get_aux_shard_state(ton::BlockIdExt blkid, td::Result<Ref<ShardState>> res) {
  LOG(DEBUG) << "in ContestValidateQuery::after_get_aux_shard_state(" << blkid.to_str() << ")";
  --pending;
  if (res.is_error()) {
    fatal_error("cannot load auxiliary masterchain state for "s + blkid.to_str() + " : " +
                res.move_as_error().to_string());
    return;
  }
  auto state = Ref<MasterchainStateQ>(res.move_as_ok());
  if (state.is_null()) {
    fatal_error("auxiliary masterchain state for "s + blkid.to_str() + " turned out to be null");
    return;
  }
  if (state->get_block_id() != blkid) {
    fatal_error("auxiliary masterchain state for "s + blkid.to_str() +
                " turned out to correspond to a different block " + state->get_block_id().to_str());
    return;
  }
  if (!register_mc_state(std::move(state))) {
    fatal_error("cannot register auxiliary masterchain state for "s + blkid.to_str());
    return;
  }
  try_validate();
}

/**
 * Checks if the Unix time and logical time of the block are valid.
 *
 * @returns True if the utime and logical time pass checks, False otherwise.
 */
bool ContestValidateQuery::check_utime_lt() {
  if (start_lt_ <= ps_.lt_) {
    return reject_query(PSTRING() << "block has start_lt " << start_lt_ << " less than or equal to lt " << ps_.lt_
                                  << " of the previous state");
  }
  if (now_ <= ps_.utime_) {
    return reject_query(PSTRING() << "block has creation time " << now_
                                  << " less than or equal to that of the previous state (" << ps_.utime_ << ")");
  }
  if (now_ <= config_->utime) {
    return reject_query(PSTRING() << "block has creation time " << now_
                                  << " less than or equal to that of the reference masterchain state ("
                                  << config_->utime << ")");
  }
  if (start_lt_ <= config_->lt) {
    return reject_query(PSTRING() << "block has start_lt " << start_lt_ << " less than or equal to lt " << config_->lt
                                  << " of the reference masterchain state");
  }
  auto lt_bound = std::max(ps_.lt_, std::max(config_->lt, max_shard_lt_));
  if (start_lt_ > lt_bound + config_->get_lt_align() * 4) {
    return reject_query(PSTRING() << "block has start_lt " << start_lt_
                                  << " which is too large without a good reason (lower bound is " << lt_bound + 1
                                  << ")");
  }
  if (end_lt_ - start_lt_ > block_limits_->lt_delta.hard()) {
    return reject_query(PSTRING() << "block increased logical time by " << end_lt_ - start_lt_
                                  << " which is larger than the hard limit " << block_limits_->lt_delta.hard());
  }
  return true;
}

/**
 * Reads the size of the outbound message queue from the previous state(s), or requests it if needed.
 *
 * @returns True if the request was successful, false otherwise.
 */
bool ContestValidateQuery::prepare_out_msg_queue_size() {
  if (ps_.out_msg_queue_size_) {
    // if after_split then out_msg_queue_size is always present, since it is calculated during split
    old_out_msg_queue_size_ = ps_.out_msg_queue_size_.value();
    out_msg_queue_size_known_ = true;
    have_out_msg_queue_size_in_state_ = true;
    return true;
  }
  if (ps_.out_msg_queue_->is_empty()) {
    old_out_msg_queue_size_ = 0;
    out_msg_queue_size_known_ = true;
    have_out_msg_queue_size_in_state_ = true;
    return true;
  }
  if (!store_out_msg_queue_size_) {  // Don't need it
    return true;
  }
  old_out_msg_queue_size_ = 0;
  out_msg_queue_size_known_ = true;
  return fatal_error("unknown queue sizes");
}


}  // namespace solution
