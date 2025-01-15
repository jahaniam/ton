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
 * Converts the error context to a string representation to show it in case of validation error.
 *
 * @returns The error context as a string.
 */
std::string ErrorCtx::as_string() const {
  std::string a;
  for (const auto& s : entries_) {
    a += s;
    a += " : ";
  }
  return a;
}

/**
 * Constructs a ContestValidateQuery object.
 *
 * @param block_id Id of the block
 * @param block_data Block data, but without state update
 * @param collated_data Collated data (proofs of shard states)
 * @param promise The Promise to return the serialized state update to
 */
ContestValidateQuery::ContestValidateQuery(BlockIdExt block_id, td::BufferSlice block_data,
                                           td::BufferSlice collated_data, td::Promise<td::BufferSlice> promise)
    : shard_(block_id.shard_full())
    , id_(block_id)
    , block_data(std::move(block_data))
    , collated_data(std::move(collated_data))
    , main_promise(std::move(promise))
    , shard_pfx_(shard_.shard)
    , shard_pfx_len_(ton::shard_prefix_length(shard_)) {
}

/**
 * Aborts the validation with the given error.
 *
 * @param error The error encountered.
 */
void ContestValidateQuery::abort_query(td::Status error) {
  (void)fatal_error(std::move(error));
}

/**
 * Rejects the validation and logs an error message.
 *
 * @param error The error message to be logged.
 * @param reason The reason for rejecting the validation.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::reject_query(std::string error, td::BufferSlice reason) {
  error = error_ctx() + error;
  LOG(WARNING) << "REJECT: aborting validation of block candidate for " << shard_.to_str() << " : " << error;
  if (main_promise) {
    main_promise.set_error(td::Status::Error(error));
  }
  stop();
  return false;
}

/**
 * Rejects the validation and logs an error message.
 *
 * @param err_msg The error message to be displayed.
 * @param error The error status.
 * @param reason The reason for rejecting the query.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::reject_query(std::string err_msg, td::Status error, td::BufferSlice reason) {
  error.ensure_error();
  return reject_query(err_msg + " : " + error.to_string(), std::move(reason));
}

/**
 * Rejects the validation and logs an error message.
 *
 * @param error The error message to be logged.
 * @param reason The reason for rejecting the validation.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::soft_reject_query(std::string error, td::BufferSlice reason) {
  error = error_ctx() + error;
  LOG(WARNING) << "SOFT REJECT: aborting validation of block candidate for " << shard_.to_str() << " : " << error;
  if (main_promise) {
    main_promise.set_error(td::Status::Error(std::move(error)));
  }
  stop();
  return false;
}

/**
 * Handles a fatal error during validation.
 *
 * @param error The error status.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::fatal_error(td::Status error) {
  error.ensure_error();
  LOG(WARNING) << "aborting validation of block candidate for " << shard_.to_str() << " : " << error.to_string();
  if (main_promise) {
    main_promise.set_error(std::move(error));
  }
  stop();
  return false;
}

/**
 * Handles a fatal error during validation.
 *
 * @param err_code Error code.
 * @param err_msg Error message.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::fatal_error(int err_code, std::string err_msg) {
  return fatal_error(td::Status::Error(err_code, error_ctx() + err_msg));
}

/**
 * Handles a fatal error during validation.
 *
 * @param err_code Error code.
 * @param err_msg Error message.
 * @param error Error status.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::fatal_error(int err_code, std::string err_msg, td::Status error) {
  error.ensure_error();
  return fatal_error(err_code, err_msg + " : " + error.to_string());
}

/**
 * Handles a fatal error during validation.
 *
 * @param err_msg Error message.
 * @param err_code Error code.
 *
 * @returns False indicating that the validation failed.
 */
bool ContestValidateQuery::fatal_error(std::string err_msg, int err_code) {
  return fatal_error(td::Status::Error(err_code, error_ctx() + err_msg));
}

/**
 * Finishes the query and sends the result to the promise.
 */
void ContestValidateQuery::finish_query() {
  if (main_promise) {
    LOG(WARNING) << "validate query done";
    main_promise.set_result(std::move(result_state_update_));
  }
  stop();
}

/*
 *
 *   INITIAL PARSE & LOAD REQUIRED DATA
 *
 */

/**
 * Starts the validation process.
 *
 * This function performs various checks on the validation parameters and the block candidate.
 * Then the function also sends requests to the ValidatorManager to fetch blocks and shard stated.
 */
void ContestValidateQuery::start_up() {
  LOG(INFO) << "validate query for " << id_.to_str() << " started";
  rand_seed_.set_zero();

  if (ShardIdFull(id_) != shard_) {
    soft_reject_query(PSTRING() << "block candidate belongs to shard " << ShardIdFull(id_).to_str()
                                << " different from current shard " << shard_.to_str());
    return;
  }
  if (workchain() != ton::basechainId) {
    soft_reject_query("only basechain is supported");
    return;
  }
  if (!shard_.is_valid_ext()) {
    reject_query("requested to validate a block for an invalid shard");
    return;
  }
  td::uint64 x = td::lower_bit64(shard_.shard);
  if (x < 8) {
    reject_query("a shard cannot be split more than 60 times");
    return;
  }
  // 3. unpack block candidate (while necessary data is being loaded)
  if (!unpack_block_candidate()) {
    reject_query("error unpacking block candidate");
    return;
  }
  if (prev_blocks.size() > 2) {
    soft_reject_query("cannot have more than two previous blocks");
    return;
  }
  if (!prev_blocks.size()) {
    soft_reject_query("must have one or two previous blocks to generate a next block");
    return;
  }
  if (prev_blocks.size() == 2) {
    if (!(shard_is_parent(shard_, ShardIdFull(prev_blocks[0])) &&
          shard_is_parent(shard_, ShardIdFull(prev_blocks[1])) && prev_blocks[0].id.shard < prev_blocks[1].id.shard)) {
      soft_reject_query(
          "the two previous blocks for a merge operation are not siblings or are not children of current shard");
      return;
    }
    for (const auto& blk : prev_blocks) {
      if (!blk.id.seqno) {
        soft_reject_query("previous blocks for a block merge operation must have non-zero seqno");
        return;
      }
    }
    // soft_reject_query("merging shards is not implemented yet");
    // return;
  } else {
    CHECK(prev_blocks.size() == 1);
    // creating next block
    if (!ShardIdFull(prev_blocks[0]).is_valid_ext()) {
      soft_reject_query("previous block does not have a valid id");
      return;
    }
    if (ShardIdFull(prev_blocks[0]) != shard_) {
      if (!shard_is_parent(ShardIdFull(prev_blocks[0]), shard_)) {
        soft_reject_query("previous block does not belong to the shard we are generating a new block for");
        return;
      }
    }
    if (after_split_) {
      // soft_reject_query("splitting shards not implemented yet");
      // return;
    }
  }
  // 4. load state(s) corresponding to previous block(s)
  prev_states.resize(prev_blocks.size());
  for (int i = 0; (unsigned)i < prev_blocks.size(); i++) {
    // 4.1. load state
    LOG(DEBUG) << "sending wait_block_state() query #" << i << " for " << prev_blocks[i].to_str() << " to Manager";
    ++pending;
    td::actor::send_closure_later(actor_id(this), &ContestValidateQuery::after_get_shard_state, i,
                                  fetch_block_state(prev_blocks[i]));
  }
  // 5. request masterchain state referred to in the block
  ++pending;
  td::actor::send_closure_later(actor_id(this), &ContestValidateQuery::after_get_mc_state,
                                fetch_block_state(mc_blkid_));
  // ...
  CHECK(pending);
}

/**
 * Unpacks and validates a block candidate.
 *
 * This function unpacks the block candidate data and performs various validation checks to ensure its integrity.
 * It checks the file hash and root hash of the block candidate against the expected values.
 * It then parses the block header and checks its validity.
 * Finally, it deserializes the collated data and extracts the collated roots.
 *
 * @returns True if the block candidate was successfully unpacked, false otherwise.
 */
bool ContestValidateQuery::unpack_block_candidate() {
  vm::BagOfCells boc1, boc2;
  // 1. deserialize block itself
  auto res1 = boc1.deserialize(block_data);
  if (res1.is_error()) {
    return reject_query("cannot deserialize block", res1.move_as_error());
  }
  if (boc1.get_root_count() != 1) {
    return reject_query("block BoC must contain exactly one root");
  }
  block_root_ = boc1.get_root_cell();
  CHECK(block_root_.not_null());
  // 3. initial block parse
  {
    auto guard = error_ctx_add_guard("parsing block header");
    try {
      if (!init_parse()) {
        return reject_query("invalid block header");
      }
    } catch (vm::VmError& err) {
      return reject_query(err.get_msg());
    } catch (vm::VmVirtError& err) {
      return reject_query(err.get_msg());
    }
  }
  // ...
  // 8. deserialize collated data
  auto res2 = boc2.deserialize(collated_data);
  if (res2.is_error()) {
    return reject_query("cannot deserialize collated data", res2.move_as_error());
  }
  int n = boc2.get_root_count();
  CHECK(n >= 0);
  for (int i = 0; i < n; i++) {
    collated_roots_.emplace_back(boc2.get_root_cell(i));
  }
  // 9. extract/classify collated data
  return extract_collated_data();
}

/**
 * Initializes the validation by parsing and checking the block header.
 *
 * @returns True if the initialization is successful, false otherwise.
 */
bool ContestValidateQuery::init_parse() {
  CHECK(block_root_.not_null());
  std::vector<BlockIdExt> prev_blks;
  bool after_split;
  auto res = block::unpack_block_prev_blk_try(block_root_, id_, prev_blks, mc_blkid_, after_split, nullptr, true);
  if (res.is_error()) {
    return reject_query("cannot unpack block header : "s + res.to_string());
  }
  CHECK(mc_blkid_.id.is_masterchain_ext());
  mc_seqno_ = mc_blkid_.seqno();
  prev_blocks = prev_blks;
  after_merge_ = prev_blocks.size() == 2;
  after_split_ = !after_merge_ && prev_blocks[0].shard_full() != shard_;
  if (after_split != after_split_) {
    // ??? impossible
    return fatal_error("after_split mismatch in block header");
  }
  block::gen::Block::Record blk;
  block::gen::BlockInfo::Record info;
  block::gen::BlockExtra::Record extra;
  block::gen::ExtBlkRef::Record mcref;  // _ ExtBlkRef = BlkMasterInfo;
  ShardIdFull shard;
  if (!(tlb::unpack_cell(block_root_, blk) && tlb::unpack_cell(blk.info, info) && !info.version &&
        block::tlb::t_ShardIdent.unpack(info.shard.write(), shard) &&
        block::gen::BlkPrevInfo{info.after_merge}.validate_ref(info.prev_ref) &&
        (!info.not_master || tlb::unpack_cell(info.master_ref, mcref)) && tlb::unpack_cell(blk.extra, extra))) {
    return reject_query("cannot unpack block header");
  }
  if (shard != shard_) {
    return reject_query("shard mismatch in the block header");
  }
  global_id_ = blk.global_id;
  vert_seqno_ = info.vert_seq_no;
  start_lt_ = info.start_lt;
  end_lt_ = info.end_lt;
  now_ = info.gen_utime;
  before_split_ = info.before_split;
  want_merge_ = info.want_merge;
  want_split_ = info.want_split;
  is_key_block_ = info.key_block;
  prev_key_seqno_ = info.prev_key_block_seqno;
  CHECK(after_split_ == info.after_split);
  if (is_key_block_) {
    LOG(INFO) << "validating key block " << id_.to_str();
  }
  if (start_lt_ >= end_lt_) {
    return reject_query("block has start_lt greater than or equal to end_lt");
  }
  if (info.after_merge && info.after_split) {
    return reject_query("a block cannot be both after merge and after split at the same time");
  }
  int shard_pfx_len = ton::shard_prefix_length(shard);
  if (info.after_split && !shard_pfx_len) {
    return reject_query("a block with empty shard prefix cannot be after split");
  }
  if (info.after_merge && shard_pfx_len >= 60) {
    return reject_query("a block split 60 times cannot be after merge");
  }
  if (is_key_block_) {
    return reject_query("a non-masterchain block cannot be a key block");
  }
  if (info.vert_seqno_incr) {
    // what about non-masterchain blocks?
    return reject_query("new blocks cannot have vert_seqno_incr set");
  }
  if (info.after_merge != after_merge_) {
    return reject_query("after_merge value mismatch in block header");
  }
  rand_seed_ = extra.rand_seed;
  created_by_ = extra.created_by;
  if (extra.custom->size_refs()) {
    return reject_query("non-masterchain block cannot have McBlockExtra");
  }
  // ...
  return true;
}

}  // namespace solution
