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

namespace {
// Helper function to validate EnqueuedMsg
bool validate_enqueued_msg(Ref<vm::CellSlice> value, td::ConstBitPtr out_msg_id, bool is_new, 
                         ton::LogicalTime start_lt, ton::LogicalTime end_lt, std::string& error);
}  // namespace

/**
 * Checks that any change in OutMsgQueue in the state is accompanied by an OutMsgDescr record in the block.
 * Also checks that the keys are correct.
 *
 * @param out_msg_id The 32+64+256-bit ID of the outbound message.
 * @param old_value The old value of the message queue entry.
 * @param new_value The new value of the message queue entry.
 *
 * @returns True if the update is valid, false otherwise.
 */
bool ContestValidateQuery::precheck_one_message_queue_update(td::ConstBitPtr out_msg_id, Ref<vm::CellSlice> old_value,
                                                             Ref<vm::CellSlice> new_value) {
  LOG(DEBUG) << "checking update of enqueued outbound message " << out_msg_id.get_int(32) << ":"
             << (out_msg_id + 32).to_hex(64) << "... with hash " << (out_msg_id + 96).to_hex(256);
  old_value = ps_.out_msg_queue_->extract_value(std::move(old_value));
  new_value = ns_.out_msg_queue_->extract_value(std::move(new_value));
  CHECK(old_value.not_null() || new_value.not_null());

  std::string error;
  if (!validate_enqueued_msg(old_value, out_msg_id, false, start_lt_, end_lt_, error) ||
      !validate_enqueued_msg(new_value, out_msg_id, true, start_lt_, end_lt_, error)) {
    return reject_query(error);
  }

  int mode = old_value.not_null() + new_value.not_null() * 2;
  static const char* m_str[] = {"", "de", "en", "re"};
  
  auto out_msg_cs = out_msg_dict_->lookup(out_msg_id + 96, 256);
  if (out_msg_cs.is_null()) {
    return reject_query(PSTRING() << "no OutMsgDescr corresponding to " << m_str[mode] 
                                << "queued message with key " << out_msg_id.to_hex(352));
  }
  
  if (mode == 3) {
    return reject_query(PSTRING() << "EnqueuedMsg with key " << out_msg_id.to_hex(352)
                                << " has been changed in the OutMsgQueue, but the key did not change");
  }

  auto q_msg_env = (old_value.not_null() ? old_value : new_value)->prefetch_ref();
  int tag = block::tlb::t_OutMsg.get_tag(*out_msg_cs);
  if (tag == 12 || tag == 13) {
    tag /= 2;
  } else if (tag == 20) {
    tag = 8;
  } else if (tag == 21) {
    tag = 9;
  }
  // mode for msg_export_{ext,new,imm,tr,deq_imm,???,deq/deq_short,tr_req,new_defer,deferred_tr}
  static const int tag_mode[10] = {0, 2, 0, 2, 1, 0, 1, 3, 0, 2};
  static const char* tag_str[10] = {"ext", "new", "imm",    "tr",        "deq_imm",
                                    "???", "deq", "tr_req", "new_defer", "deferred_tr"};
  if (tag < 0 || tag >= 10 || !(tag_mode[tag] & mode)) {
    return reject_query(PSTRING() << "OutMsgDescr corresponding to " << m_str[mode] << "queued message with key "
                                  << out_msg_id.to_hex(352) << " has invalid tag " << tag << "(" << tag_str[tag & 7]
                                  << ")");
  }
  bool is_short = (tag == 6 && (out_msg_cs->prefetch_ulong(4) &
                                1));  // msg_export_deq_short does not contain true MsgEnvelope / Message
  Ref<vm::Cell> msg_env, msg;
  td::Bits256 msg_env_hash;
  block::gen::OutMsg::Record_msg_export_deq_short deq_short;
  if (!is_short) {
    msg_env = out_msg_cs->prefetch_ref();
    if (msg_env.is_null()) {
      return reject_query("OutMsgDescr for "s + out_msg_id.to_hex(352) + " is invalid (contains no MsgEnvelope)");
    }
    msg_env_hash = msg_env->get_hash().bits();
    msg = vm::load_cell_slice(msg_env).prefetch_ref();
    if (msg.is_null()) {
      return reject_query("OutMsgDescr for "s + out_msg_id.to_hex(352) + " is invalid (contains no message)");
    }
    if (msg->get_hash().as_bitslice() != out_msg_id + 96) {
      return reject_query("OutMsgDescr for "s + (out_msg_id + 96).to_hex(256) +
                          " contains a message with different hash "s + msg->get_hash().bits().to_hex(256));
    }
  } else {
    if (!tlb::csr_unpack(out_msg_cs, deq_short)) {  // parsing msg_export_deq_short$1101 ...
      return reject_query("OutMsgDescr for "s + out_msg_id.to_hex(352) +
                          " is invalid (cannot unpack msg_export_deq_short)");
    }
    msg_env_hash = deq_short.msg_env_hash;
  }
  //
  if (mode == 1) {
    // dequeued message
    if (tag == 7) {
      // this is a msg_export_tr_req$111, a re-queued transit message (after merge)
      // check that q_msg_env still contains msg
      auto q_msg = vm::load_cell_slice(q_msg_env).prefetch_ref();
      if (q_msg.is_null()) {
        return reject_query("MsgEnvelope in the old outbound queue with key "s + out_msg_id.to_hex(352) +
                            " is invalid");
      }
      if (q_msg->get_hash().as_bitslice() != msg->get_hash().bits()) {
        return reject_query("MsgEnvelope in the old outbound queue with key "s + out_msg_id.to_hex(352) +
                            " contains a Message with incorrect hash " + q_msg->get_hash().bits().to_hex(256));
      }
      auto import = out_msg_cs->prefetch_ref(1);
      if (import.is_null()) {
        return reject_query("OutMsgDescr for "s + out_msg_id.to_hex(352) + " is not a valid msg_export_tr_req");
      }
      auto import_cs = vm::load_cell_slice(std::move(import));
      int import_tag = (int)import_cs.prefetch_ulong(3);
      if (import_tag != 4) {
        // must be msg_import_tr$100
        return reject_query(PSTRING() << "OutMsgDescr for " << out_msg_id.to_hex(352)
                                      << " refers to a reimport InMsgDescr with invalid tag " << import_tag
                                      << " instead of msg_import_tr$100");
      }
      auto in_msg_env = import_cs.prefetch_ref();
      if (in_msg_env.is_null()) {
        return reject_query("OutMsgDescr for "s + out_msg_id.to_hex(352) +
                            " is a msg_export_tr_req referring to an invalid reimport InMsgDescr");
      }
      if (in_msg_env->get_hash().as_bitslice() != q_msg_env->get_hash().bits()) {
        return reject_query("OutMsgDescr corresponding to dequeued message with key "s + out_msg_id.to_hex(352) +
                            " is a msg_export_tr_req referring to a reimport InMsgDescr that contains a MsgEnvelope "
                            "distinct from that originally kept in the old queue");
      }
    } else if (msg_env_hash != q_msg_env->get_hash().bits()) {
      return reject_query("OutMsgDescr corresponding to dequeued message with key "s + out_msg_id.to_hex(352) +
                          " contains a MsgEnvelope distinct from that originally kept in the old queue");
    }
  } else {
    // enqueued message
    if (msg_env_hash != q_msg_env->get_hash().bits()) {
      return reject_query("OutMsgDescr corresponding to "s + m_str[mode] + "queued message with key "s +
                          out_msg_id.to_hex(352) +
                          " contains a MsgEnvelope distinct from that stored in the new queue");
    }
  }
  // in all cases above, we have to check that all 352-bit key is correct (including first 96 bits)
  // otherwise we might not be able to correctly recover OutMsgQueue entries starting from OutMsgDescr later
  // or we might have several OutMsgQueue entries with different 352-bit keys all having the same last 256 bits (with the message hash)
  if (is_short) {
    // check out_msg_id using fields next_workchain:int32 next_addr_pfx:uint64 of msg_export_deq_short$1101
    if (out_msg_id.get_int(32) != deq_short.next_workchain ||
        (out_msg_id + 32).get_uint(64) != deq_short.next_addr_pfx) {
      return reject_query(
          PSTRING() << "OutMsgQueue entry with key " << out_msg_id.to_hex(352)
                    << " corresponds to msg_export_deq_short OutMsg entry with incorrect next hop parameters "
                    << deq_short.next_workchain << "," << deq_short.next_addr_pfx);
    }
  }
  td::BitArray<352> key;
  if (!block::compute_out_msg_queue_key(q_msg_env, key)) {
    return reject_query("OutMsgQueue entry with key "s + out_msg_id.to_hex(352) +
                        " refers to a MsgEnvelope that cannot be unpacked");
  }
  if (key != out_msg_id) {
    return reject_query("OutMsgQueue entry with key "s + out_msg_id.to_hex(352) +
                        " contains a MsgEnvelope that should have been stored under different key " + key.to_hex());
  }
  return true;
}

namespace {
bool validate_enqueued_msg(Ref<vm::CellSlice> value, td::ConstBitPtr out_msg_id, bool is_new, 
                         ton::LogicalTime start_lt, ton::LogicalTime end_lt, std::string& error) {
    if (value.not_null() && value->size_ext() != 0x10040) {
        error = PSTRING() << (is_new ? "new" : "old") << " EnqueuedMsg with key " << out_msg_id.to_hex(352) << " is invalid";
        return false;
    }
    
    if (value.not_null()) {
        if (!block::gen::t_EnqueuedMsg.validate_csr(value) || !block::tlb::t_EnqueuedMsg.validate_csr(value)) {
            error = PSTRING() << (is_new ? "new" : "old") << " EnqueuedMsg with key " << out_msg_id.to_hex(352) 
                           << " failed validity checks";
            return false;
        }
        
        ton::LogicalTime enqueued_lt = value->prefetch_ulong(64);
        if (is_new) {
            if (enqueued_lt < start_lt || enqueued_lt >= end_lt) {
                error = PSTRING() << "new EnqueuedMsg with key " << out_msg_id.to_hex(352) 
                                << " has enqueued_lt=" << enqueued_lt 
                                << " outside of block's range " << start_lt << " .. " << end_lt;
                return false;
            }
        } else {
            if (enqueued_lt >= start_lt) {
                error = PSTRING() << "old EnqueuedMsg with key " << out_msg_id.to_hex(352) 
                                << " has enqueued_lt=" << enqueued_lt 
                                << " greater than or equal to block's start_lt=" << start_lt;
                return false;
            }
        }
    }
    return true;
}
}  // namespace

/**
 * Performs a pre-check on the difference between the old and new outbound message queues.
 *
 * @returns True if the pre-check is successful, false otherwise.
 */
bool ContestValidateQuery::precheck_message_queue_update() {
  LOG(INFO) << "pre-checking the difference between the old and the new outbound message queues";
  try {
    CHECK(ps_.out_msg_queue_ && ns_.out_msg_queue_);
    CHECK(out_msg_dict_);
    if (!ps_.out_msg_queue_->scan_diff(
            *ns_.out_msg_queue_,
            [this](td::ConstBitPtr key, int key_len, Ref<vm::CellSlice> old_val_extra,
                   Ref<vm::CellSlice> new_val_extra) {
              CHECK(key_len == 352);
              return precheck_one_message_queue_update(key, std::move(old_val_extra), std::move(new_val_extra));
            },
            2 /* check augmentation of changed nodes in the new dict */)) {
      return reject_query("invalid OutMsgQueue dictionary in the new state");
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid OutMsgQueue dictionary difference between the old and the new state: "s +
                        err.get_msg());
  }
  if (store_out_msg_queue_size_) {
  } else {
    if (ns_.out_msg_queue_size_) {
      return reject_query("outbound message queue size in the new state is present, but shouldn't");
    }
  }
  return true;
}

/**
 * Performs a check on the difference between the old and new dispatch queues for one account.
 *
 * @param addr The 256-bit address of the account.
 * @param old_queue_csr The old value of the account dispatch queue.
 * @param new_queue_csr The new value of the account dispatch queue.
 *
 * @returns True if the check is successful, false otherwise.
 */
bool ContestValidateQuery::check_account_dispatch_queue_update(td::Bits256 addr, Ref<vm::CellSlice> old_queue_csr,
                                                               Ref<vm::CellSlice> new_queue_csr) {
  vm::Dictionary old_dict{64};
  td::uint64 old_dict_size = 0;
  if (!block::unpack_account_dispatch_queue(old_queue_csr, old_dict, old_dict_size)) {
    return reject_query(PSTRING() << "invalid AccountDispatchQueue for " << addr.to_hex() << " in the old state");
  }
  vm::Dictionary new_dict{64};
  td::uint64 new_dict_size = 0;
  if (!block::unpack_account_dispatch_queue(new_queue_csr, new_dict, new_dict_size)) {
    return reject_query(PSTRING() << "invalid AccountDispatchQueue for " << addr.to_hex() << " in the new state");
  }
  td::uint64 expected_dict_size = old_dict_size;
  LogicalTime max_removed_lt = 0;
  LogicalTime min_added_lt = (LogicalTime)-1;
  bool res = old_dict.scan_diff(
      new_dict, [&](td::ConstBitPtr key, int key_len, Ref<vm::CellSlice> old_val, Ref<vm::CellSlice> new_val) {
        CHECK(key_len == 64);
        CHECK(old_val.not_null() || new_val.not_null());
        if (old_val.not_null() && new_val.not_null()) {
          return false;
        }
        td::uint64 lt = key.get_uint(64);
        block::gen::EnqueuedMsg::Record rec;
        if (old_val.not_null()) {
          LOG(DEBUG) << "removed message from DispatchQueue: account=" << addr.to_hex() << ", lt=" << lt;
          --expected_dict_size;
          if (!block::tlb::csr_unpack(old_val, rec)) {
            return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex());
          }
        } else {
          LOG(DEBUG) << "added message to DispatchQueue: account=" << addr.to_hex() << ", lt=" << lt;
          ++expected_dict_size;
          if (!block::tlb::csr_unpack(new_val, rec)) {
            return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex());
          }
        }
        if (lt != rec.enqueued_lt) {
          return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex()
                                        << ": lt mismatch (" << lt << " != " << rec.enqueued_lt << ")");
        }
        block::tlb::MsgEnvelope::Record_std env;
        if (!block::gen::t_MsgEnvelope.validate_ref(rec.out_msg) || !block::tlb::unpack_cell(rec.out_msg, env)) {
          return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex());
        }
        if (env.emitted_lt) {
          return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex()
                                        << ", lt=" << lt << ": unexpected emitted_lt");
        }
        unsigned long long created_lt;
        vm::CellSlice msg_cs = vm::load_cell_slice(env.msg);
        if (!block::tlb::t_Message.get_created_lt(msg_cs, created_lt)) {
          return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex()
                                        << ": cannot get created_lt");
        }
        if (lt != created_lt) {
          return reject_query(PSTRING() << "invalid EnqueuedMsg in AccountDispatchQueue for " << addr.to_hex()
                                        << ": lt mismatch (" << lt << " != " << created_lt << ")");
        }
        if (old_val.not_null()) {
          removed_dispatch_queue_messages_[{addr, lt}] = rec.out_msg;
          max_removed_lt = std::max(max_removed_lt, lt);
        } else {
          new_dispatch_queue_messages_[{addr, lt}] = rec.out_msg;
          min_added_lt = std::min(min_added_lt, lt);
        }
        return true;
      });
  if (!res) {
    return reject_query(PSTRING() << "invalid AccountDispatchQueue diff for account " << addr.to_hex());
  }
  if (expected_dict_size != new_dict_size) {
    return reject_query(PSTRING() << "invalid count in AccountDispatchQuery for " << addr.to_hex()
                                  << ": expected=" << expected_dict_size << ", found=" << new_dict_size);
  }
  if (!new_dict.is_empty()) {
    td::BitArray<64> new_min_lt;
    CHECK(new_dict.get_minmax_key(new_min_lt).not_null());
    if (new_min_lt.to_ulong() <= max_removed_lt) {
      return reject_query(PSTRING() << "invalid AccountDispatchQuery update for " << addr.to_hex()
                                    << ": max removed lt is " << max_removed_lt << ", but lt=" << new_min_lt.to_ulong()
                                    << " is still in queue");
    }
  }
  if (!old_dict.is_empty()) {
    td::BitArray<64> old_max_lt;
    CHECK(old_dict.get_minmax_key(old_max_lt, true).not_null());
    if (old_max_lt.to_ulong() >= min_added_lt) {
      return reject_query(PSTRING() << "invalid AccountDispatchQuery update for " << addr.to_hex()
                                    << ": min added lt is " << min_added_lt << ", but lt=" << old_max_lt.to_ulong()
                                    << " was present in the queue");
    }
    if (max_removed_lt != old_max_lt.to_ulong()) {
      // Some old messages are still in DispatchQueue, meaning that all new messages from this account must be deferred
      account_expected_defer_all_messages_.insert(addr);
    }
  }
  if (old_dict_size > 0 && max_removed_lt != 0) {
    ++processed_account_dispatch_queues_;
  }
  return true;
}

/**
 * Pre-check the difference between the old and new dispatch queues and put the difference to
 * new_dispatch_queue_messages_, old_dispatch_queue_messages_
 *
 * @returns True if the pre-check and unpack is successful, false otherwise.
 */
bool ContestValidateQuery::unpack_dispatch_queue_update() {
  LOG(INFO) << "checking the difference between the old and the new dispatch queues";
  try {
    CHECK(ps_.dispatch_queue_ && ns_.dispatch_queue_);
    CHECK(out_msg_dict_);
    bool res = ps_.dispatch_queue_->scan_diff(
        *ns_.dispatch_queue_,
        [this](td::ConstBitPtr key, int key_len, Ref<vm::CellSlice> old_val_extra, Ref<vm::CellSlice> new_val_extra) {
          CHECK(key_len == 256);
          return check_account_dispatch_queue_update(key, ps_.dispatch_queue_->extract_value(std::move(old_val_extra)),
                                                     ns_.dispatch_queue_->extract_value(std::move(new_val_extra)));
        },
        2 /* check augmentation of changed nodes in the new dict */);
    if (!res) {
      return reject_query("invalid DispatchQueue dictionary in the new state");
    }

    if (have_out_msg_queue_size_in_state_ &&
        old_out_msg_queue_size_ <= compute_phase_cfg_.size_limits.defer_out_queue_size_limit) {
      // Check that at least one message was taken from each AccountDispatchQueue
      try {
        have_unprocessed_account_dispatch_queue_ = false;
        td::uint64 total_account_dispatch_queues = 0;
        ps_.dispatch_queue_->check_for_each([&](Ref<vm::CellSlice>, td::ConstBitPtr, int n) -> bool {
          ++total_account_dispatch_queues;
          if (total_account_dispatch_queues > processed_account_dispatch_queues_) {
            return false;
          }
          return true;
        });
        have_unprocessed_account_dispatch_queue_ =
            (total_account_dispatch_queues != processed_account_dispatch_queues_);
      } catch (vm::VmVirtError&) {
        // VmVirtError can happen if we have only a proof of ShardState
        have_unprocessed_account_dispatch_queue_ = true;
      }
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid DispatchQueue dictionary difference between the old and the new state: "s +
                        err.get_msg());
  }
  return true;
}

/**
 * Updates the maximum processed logical time and hash value.
 *
 * @param lt The logical time to compare against the current maximum processed logical time.
 * @param hash The hash value to compare against the current maximum processed hash value.
 *
 * @returns True if the update was successful, false otherwise.
 */
bool ContestValidateQuery::update_max_processed_lt_hash(ton::LogicalTime lt, const ton::Bits256& hash) {
  if (proc_lt_ < lt || (proc_lt_ == lt && proc_hash_ < hash)) {
    proc_lt_ = lt;
    proc_hash_ = hash;
  }
  return true;
}

/**
 * Updates the minimum enqueued logical time and hash values.
 *
 * @param lt The logical time to compare.
 * @param hash The hash value to compare.
 *
 * @returns True if the update was successful, false otherwise.
 */
bool ContestValidateQuery::update_min_enqueued_lt_hash(ton::LogicalTime lt, const ton::Bits256& hash) {
  if (lt < min_enq_lt_ || (lt == min_enq_lt_ && hash < min_enq_hash_)) {
    min_enq_lt_ = lt;
    min_enq_hash_ = hash;
  }
  return true;
}

/**
 * Checks that the MsgEnvelope was present in the output queue of a neighbor, and that it has not been processed before.
 *
 * @param msg_env The message envelope of the imported message.
 *
 * @returns True if the imported internal message passes checks, false otherwise.
 */
bool ContestValidateQuery::check_imported_message(Ref<vm::Cell> msg_env) {
  block::tlb::MsgEnvelope::Record_std env;
  block::gen::CommonMsgInfo::Record_int_msg_info info;
  ton::AccountIdPrefixFull src_prefix, dest_prefix, cur_prefix, next_prefix;
  if (!(msg_env.not_null() && tlb::unpack_cell(msg_env, env) && tlb::unpack_cell_inexact(env.msg, info) &&
        block::tlb::t_MsgAddressInt.get_prefix_to(std::move(info.src), src_prefix) &&
        block::tlb::t_MsgAddressInt.get_prefix_to(std::move(info.dest), dest_prefix) &&
        block::interpolate_addr_to(src_prefix, dest_prefix, env.cur_addr, cur_prefix) &&
        block::interpolate_addr_to(src_prefix, dest_prefix, env.next_addr, next_prefix))) {
    return reject_query("cannot unpack MsgEnvelope of an imported internal message with hash "s +
                        (env.msg.not_null() ? env.msg->get_hash().to_hex() : "(unknown)"));
  }
  if (!ton::shard_contains(shard_, next_prefix)) {
    return reject_query("imported message with hash "s + env.msg->get_hash().to_hex() + " has next hop address " +
                        next_prefix.to_str() + "... not in this shard");
  }
  td::BitArray<32 + 64 + 256> key;
  key.bits().store_int(next_prefix.workchain, 32);
  (key.bits() + 32).store_int(next_prefix.account_id_prefix, 64);
  (key.bits() + 96).copy_from(env.msg->get_hash().bits(), 256);
  for (const auto& nb : neighbors_) {
    if (!nb.is_disabled() && nb.contains(cur_prefix)) {
      CHECK(nb.out_msg_queue);
      auto nqv = nb.out_msg_queue->lookup_with_extra(key.bits(), key.size());
      if (nqv.is_null()) {
        return reject_query("imported internal message with hash "s + env.msg->get_hash().to_hex() +
                            " and previous address " + cur_prefix.to_str() + "..., next hop address " +
                            next_prefix.to_str() + " could not be found in the outbound message queue of neighbor " +
                            nb.blk_.to_str() + " under key " + key.to_hex());
      }
      block::EnqueuedMsgDescr enq_msg_descr;
      unsigned long long created_lt;
      if (!(nqv.write().fetch_ulong_bool(64, created_lt)  // augmentation
            && enq_msg_descr.unpack(nqv.write())          // unpack EnqueuedMsg
            && enq_msg_descr.check_key(key.bits())        // check key
            && enq_msg_descr.lt_ == created_lt)) {
        return reject_query("imported internal message from the outbound message queue of neighbor " +
                            nb.blk_.to_str() + " under key " + key.to_hex() +
                            " has an invalid EnqueuedMsg record in that queue");
      }
      if (enq_msg_descr.msg_env_->get_hash() != msg_env->get_hash()) {
        return reject_query("imported internal message from the outbound message queue of neighbor " +
                            nb.blk_.to_str() + " under key " + key.to_hex() +
                            " had a different MsgEnvelope in that outbound message queue");
      }
      if (ps_.processed_upto_->already_processed(enq_msg_descr)) {
        return reject_query(PSTRING() << "imported internal message with hash " << env.msg->get_hash().bits()
                                      << " and lt=" << created_lt
                                      << " has been already imported by a previous block of this shardchain");
      }
      update_max_processed_lt_hash(enq_msg_descr.lt_, enq_msg_descr.hash_);
      return true;
    }
  }
  return reject_query("imported internal message with hash "s + env.msg->get_hash().to_hex() +
                      " and previous address " + cur_prefix.to_str() + "..., next hop address " + next_prefix.to_str() +
                      " has previous address not belonging to any neighbor");
}

/**
 * Checks if the given input message is a special message.
 * A message is considered special if it recovers fees or mints extra currencies.
 *
 * @param in_msg The input message to be checked.
 *
 * @returns True if the input message is special, False otherwise.
 */
bool ContestValidateQuery::is_special_in_msg(const vm::CellSlice& in_msg) const {
  return (recover_create_msg_.not_null() && vm::load_cell_slice(recover_create_msg_).contents_equal(in_msg)) ||
         (mint_msg_.not_null() && vm::load_cell_slice(mint_msg_).contents_equal(in_msg));
}

/**
 * Checks the validity of an inbound message listed in InMsgDescr.
 *
 * @param key The 256-bit key of the inbound message.
 * @param in_msg The inbound message to be checked serialized using InMsg TLB-scheme.
 *
 * @returns True if the inbound message is valid, false otherwise.
 */
bool ContestValidateQuery::check_in_msg(td::ConstBitPtr key, Ref<vm::CellSlice> in_msg) {
  // Fast path checks
  if (in_msg.is_null()) {
    return reject_query("InMsg is null");
  }
  
  const int tag = block::gen::t_InMsg.get_tag(*in_msg);
  if (tag < 0) {
    return reject_query("Invalid InMsg tag");
  }

  // Common variables
  ton::StdSmcAddress src_addr, dest_addr;
  ton::WorkchainId src_wc, dest_wc;
  Ref<vm::CellSlice> src, dest;
  Ref<vm::Cell> transaction;
  Ref<vm::Cell> msg, msg_env, tr_msg_env;
  block::tlb::MsgEnvelope::Record_std env;
  block::gen::CommonMsgInfo::Record_int_msg_info info;
  ton::AccountIdPrefixFull src_prefix, dest_prefix, cur_prefix, next_prefix;
  td::RefInt256 fwd_fee, orig_fwd_fee;
  bool from_dispatch_queue = false;

  // Optimized message handling
  switch (tag) {
    case block::gen::InMsg::msg_import_ext: {
      // Optimized external message handling
      block::gen::CommonMsgInfo::Record_ext_in_msg_info info_ext;
      vm::CellSlice cs{*in_msg};
      
      if (!block::gen::t_InMsg.unpack_msg_import_ext(cs, msg, transaction) ||
          msg->get_hash().as_bitslice() != key) {
        return reject_query("Invalid external message or hash mismatch");
      }
      
      if (!tlb::unpack_cell_inexact(msg, info_ext)) {
        return reject_query("Invalid external message format");
      }
      
      dest_prefix = block::tlb::t_MsgAddressInt.get_prefix(info_ext.dest);
      if (!dest_prefix.is_valid() || !ton::shard_contains(shard_, dest_prefix)) {
        return reject_query("Invalid destination address or shard mismatch");
      }
      
      dest = std::move(info_ext.dest);
      if (!block::tlb::t_MsgAddressInt.extract_std_address(dest, dest_wc, dest_addr)) {
        return reject_query("Cannot unpack destination address");
      }
      break;
    }
    case block::gen::InMsg::msg_import_imm: {
      // msg_import_imm$011 in_msg:^MsgEnvelope transaction:^Transaction fwd_fee:Grams
      // importing and processing an internal message generated in this very block
      block::gen::InMsg::Record_msg_import_imm inp;
      unsigned long long created_lt = 0;
      CHECK(tlb::csr_unpack(in_msg, inp) && tlb::unpack_cell(inp.in_msg, env) &&
            block::tlb::t_MsgEnvelope.get_emitted_lt(vm::load_cell_slice(inp.in_msg), created_lt) &&
            (fwd_fee = block::tlb::t_Grams.as_integer(std::move(inp.fwd_fee))).not_null());
      transaction = std::move(inp.transaction);
      msg_env = std::move(inp.in_msg);
      msg = env.msg;
      if (!is_special_in_msg(*in_msg)) {
        update_max_processed_lt_hash(created_lt, msg->get_hash().bits());
      }
      // ...
      break;
    }
    case block::gen::InMsg::msg_import_fin: {
      // msg_import_fin$100 in_msg:^MsgEnvelope transaction:^Transaction fwd_fee:Grams
      // importing and processing an internal message with destination in this shard
      block::gen::InMsg::Record_msg_import_fin inp;
      CHECK(tlb::csr_unpack(in_msg, inp) && tlb::unpack_cell(inp.in_msg, env) &&
            (fwd_fee = block::tlb::t_Grams.as_integer(std::move(inp.fwd_fee))).not_null());
      transaction = std::move(inp.transaction);
      msg_env = std::move(inp.in_msg);
      msg = env.msg;
      // ...
      break;
    }
    case block::gen::InMsg::msg_import_tr: {
      // msg_import_tr$101 in_msg:^MsgEnvelope out_msg:^MsgEnvelope transit_fee:Grams
      // importing and relaying a (transit) internal message with destination outside this shard
      block::gen::InMsg::Record_msg_import_tr inp;
      CHECK(tlb::csr_unpack(in_msg, inp) && tlb::unpack_cell(inp.in_msg, env) &&
            (fwd_fee = block::tlb::t_Grams.as_integer(std::move(inp.transit_fee))).not_null());
      msg_env = std::move(inp.in_msg);
      msg = env.msg;
      tr_msg_env = std::move(inp.out_msg);
      // ...
      break;
    }
    case block::gen::InMsg::msg_import_ihr:
      // msg_import_ihr$010 msg:^(Message Any) transaction:^Transaction ihr_fee:Grams proof_created:^Cell
      return reject_query("InMsg with key "s + key.to_hex(256) +
                          " is a msg_import_ihr, but IHR messages are not enabled in this version");
    case block::gen::InMsg::msg_discard_tr:
      // msg_discard_tr$111 in_msg:^MsgEnvelope transaction_id:uint64 fwd_fee:Grams proof_delivered:^Cell
      return reject_query("InMsg with key "s + key.to_hex(256) +
                          " is a msg_discard_tr, but IHR messages are not enabled in this version");
    case block::gen::InMsg::msg_discard_fin:
      // msg_discard_fin$110 in_msg:^MsgEnvelope transaction_id:uint64 fwd_fee:Grams
      return reject_query("InMsg with key "s + key.to_hex(256) +
                          " is a msg_discard_fin, but IHR messages are not enabled in this version");
    case block::gen::InMsg::msg_import_deferred_fin: {
      from_dispatch_queue = true;
      // msg_import_deferredfin$00100 in_msg:^MsgEnvelope transaction:^Transaction fwd_fee:Grams
      // importing and processing an internal message from DispatchQueue with destination in this shard
      block::gen::InMsg::Record_msg_import_deferred_fin inp;
      CHECK(tlb::csr_unpack(in_msg, inp) && tlb::unpack_cell(inp.in_msg, env) &&
            (fwd_fee = block::tlb::t_Grams.as_integer(std::move(inp.fwd_fee))).not_null());
      transaction = std::move(inp.transaction);
      msg_env = std::move(inp.in_msg);
      msg = env.msg;
      // ...
      break;
    }
    case block::gen::InMsg::msg_import_deferred_tr: {
      from_dispatch_queue = true;
      // msg_import_deferred_tr$00101 in_msg:^MsgEnvelope out_msg:^MsgEnvelope
      // importing and enqueueing internal message from DispatchQueue
      block::gen::InMsg::Record_msg_import_deferred_tr inp;
      CHECK(tlb::csr_unpack(in_msg, inp) && tlb::unpack_cell(inp.in_msg, env));
      fwd_fee = td::zero_refint();
      msg_env = std::move(inp.in_msg);
      msg = env.msg;
      tr_msg_env = std::move(inp.out_msg);
      // ...
      break;
    }
    default:
      return reject_query(PSTRING() << "InMsg with key " << key.to_hex(256) << " has impossible tag " << tag);
  }
  if (have_unprocessed_account_dispatch_queue_ && tag != block::gen::InMsg::msg_import_ext &&
      tag != block::gen::InMsg::msg_import_deferred_tr && tag != block::gen::InMsg::msg_import_deferred_fin) {
    // Collator is requeired to take at least one message from each AccountDispatchQueue
    // (unless the block is full or unless out_msg_queue_size is big)
    // If some AccountDispatchQueue is unporcessed then it's not allowed to import other messages except for externals
    return reject_query("required DispatchQueue processing is not done, but some other internal messages are imported");
  }
  // common checks for all (non-external) inbound messages
  CHECK(msg.not_null());
  if (msg->get_hash().as_bitslice() != key) {
    return reject_query("InMsg with key "s + key.to_hex(256) + " refers to a message with different hash " +
                        msg->get_hash().to_hex());
  }
  if (tag != block::gen::InMsg::msg_import_ext) {
    // unpack int_msg_info$0 ... = CommonMsgInfo, especially message addresses
    if (!tlb::unpack_cell_inexact(msg, info)) {
      return reject_query("InMsg with key "s + key.to_hex(256) +
                          " is not a msg_import_ext$000, but it does not refer to an inbound internal message");
    }
    // extract source, current, next hop and destination address prefixes
    dest_prefix = block::tlb::t_MsgAddressInt.get_prefix(info.dest);
    if (!dest_prefix.is_valid()) {
      return reject_query("destination of inbound internal message with hash "s + key.to_hex(256) +
                          " is an invalid blockchain address");
    }
    src_prefix = block::tlb::t_MsgAddressInt.get_prefix(info.src);
    if (!src_prefix.is_valid()) {
      return reject_query("source of inbound internal message with hash "s + key.to_hex(256) +
                          " is an invalid blockchain address");
    }
    cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.cur_addr);
    next_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.next_addr);
    if (!(cur_prefix.is_valid() && next_prefix.is_valid())) {
      return reject_query("cannot compute current and next hop addresses of inbound internal message with hash "s +
                          key.to_hex(256));
    }
    // check that next hop is nearer to the destination than the current address
    if (count_matching_bits(dest_prefix, next_prefix) < count_matching_bits(dest_prefix, cur_prefix)) {
      return reject_query("next hop address "s + next_prefix.to_str() + "... of inbound internal message with hash " +
                          key.to_hex(256) + " is further from its destination " + dest_prefix.to_str() +
                          "... than its current address " + cur_prefix.to_str() + "...");
    }
    // next hop address must belong to this shard (otherwise we should never had imported this message)
    if (!ton::shard_contains(shard_, next_prefix)) {
      return reject_query("next hop address "s + next_prefix.to_str() + "... of inbound internal message with hash " +
                          key.to_hex(256) + " does not belong to the current block's shard " + shard_.to_str());
    }
    // next hop may coincide with current address only if destination is already reached (or it is deferred message)
    if (!from_dispatch_queue && next_prefix == cur_prefix && cur_prefix != dest_prefix) {
      return reject_query(
          "next hop address "s + next_prefix.to_str() + "... of inbound internal message with hash " + key.to_hex(256) +
          " coincides with its current address, but this message has not reached its final destination " +
          dest_prefix.to_str() + "... yet");
    }
    if (from_dispatch_queue && next_prefix != cur_prefix) {
      return reject_query("next hop address "s + next_prefix.to_str() + "... of deferred internal message with hash " +
                          key.to_hex(256) + " must coincide with its current prefix "s + cur_prefix.to_str() + "..."s);
    }
    // if a message is processed by a transaction, it must have destination inside the current shard
    if (transaction.not_null() && !ton::shard_contains(shard_, dest_prefix)) {
      return reject_query("inbound internal message with hash "s + key.to_hex(256) + " has destination address " +
                          dest_prefix.to_str() + "... not in this shard, but it is processed nonetheless");
    }
    // if a message is not processed by a transaction, its final destination must be outside this shard,
    // or it is a deferred message (dispatch queue -> out msg queue)
    if (tag != block::gen::InMsg::msg_import_deferred_tr && transaction.is_null() &&
        ton::shard_contains(shard_, dest_prefix)) {
      return reject_query("inbound internal message with hash "s + key.to_hex(256) + " has destination address " +
                          dest_prefix.to_str() + "... in this shard, but it is not processed by a transaction");
    }
    src = std::move(info.src);
    dest = std::move(info.dest);
    // unpack complete destination address if it is inside this shard
    if (transaction.not_null() && !block::tlb::t_MsgAddressInt.extract_std_address(dest, dest_wc, dest_addr)) {
      return reject_query("cannot unpack destination address of inbound internal message with hash "s +
                          key.to_hex(256));
    }
    // unpack original forwarding fee
    orig_fwd_fee = block::tlb::t_Grams.as_integer(info.fwd_fee);
    CHECK(orig_fwd_fee.not_null());
    if (env.fwd_fee_remaining > orig_fwd_fee) {
      return reject_query("inbound internal message with hash "s + key.to_hex(256) + " has remaining forwarding fee " +
                          td::dec_string(env.fwd_fee_remaining) + " larger than the original (total) forwarding fee " +
                          td::dec_string(orig_fwd_fee));
    }
    // Unpacr src address
    if (!block::tlb::t_MsgAddressInt.extract_std_address(src, src_wc, src_addr)) {
      return reject_query("cannot unpack source address of inbound external message with hash "s + key.to_hex(256));
    }
  }

  if (from_dispatch_queue) {
    // Check that the message was removed from DispatchQueue
    LogicalTime lt = info.created_lt;
    auto it = removed_dispatch_queue_messages_.find({src_addr, lt});
    if (it == removed_dispatch_queue_messages_.end()) {
      return reject_query(PSTRING() << "deferred InMsg with src_addr=" << src_addr.to_hex() << ", lt=" << lt
                                    << " was not removed from the dispatch queue");
    }
    // InMsg msg_import_deferred_* has emitted_lt in MessageEnv, but this emitted_lt is not present in DispatchQueue
    Ref<vm::Cell> dispatched_msg_env = it->second;
    td::Ref<vm::Cell> expected_msg_env;
    if (!env.emitted_lt) {
      return reject_query(PSTRING() << "no dispatch_lt in deferred InMsg with src_addr=" << src_addr.to_hex()
                                    << ", lt=" << lt);
    }
    auto emitted_lt = env.emitted_lt.value();
    if (emitted_lt < start_lt_ || emitted_lt > end_lt_) {
      return reject_query(PSTRING() << "dispatch_lt in deferred InMsg with src_addr=" << src_addr.to_hex()
                                    << ", lt=" << lt << " is not between start and end of the block");
    }
    auto env2 = env;
    env2.emitted_lt = {};
    CHECK(block::tlb::pack_cell(expected_msg_env, env2));
    if (dispatched_msg_env->get_hash() != expected_msg_env->get_hash()) {
      return reject_query(PSTRING() << "deferred InMsg with src_addr=" << src_addr.to_hex() << ", lt=" << lt
                                    << " msg envelope hasg mismatch: " << dispatched_msg_env->get_hash().to_hex()
                                    << " in DispatchQueue, " << expected_msg_env->get_hash().to_hex() << " expected");
    }
    removed_dispatch_queue_messages_.erase(it);
    if (tag == block::gen::InMsg::msg_import_deferred_fin) {
      msg_emitted_lt_.emplace_back(src_addr, lt, env.emitted_lt.value());
    }
  }

  if (transaction.not_null()) {
    // check that the transaction reference is valid, and that it points to a Transaction which indeed processes this input message
    if (!is_valid_transaction_ref(transaction)) {
      return reject_query(
          "InMsg corresponding to inbound message with key "s + key.to_hex(256) +
          " contains an invalid Transaction reference (transaction not in the block's transaction list)");
    }
    if (!block::is_transaction_in_msg(transaction, msg)) {
      return reject_query("InMsg corresponding to inbound message with key "s + key.to_hex(256) +
                          " refers to transaction that does not process this inbound message");
    }
    ton::StdSmcAddress trans_addr;
    ton::LogicalTime trans_lt;
    CHECK(block::get_transaction_id(transaction, trans_addr, trans_lt));
    if (dest_addr != trans_addr) {
      block::gen::t_InMsg.print(std::cerr, *in_msg);
      return reject_query(PSTRING() << "InMsg corresponding to inbound message with hash " << key.to_hex(256)
                                    << " and destination address " << dest_addr.to_hex()
                                    << " claims that the message is processed by transaction " << trans_lt
                                    << " of another account " << trans_addr.to_hex());
    }
  }

  if (tag == block::gen::InMsg::msg_import_ext) {
    return true;  // nothing to check more for external messages
  }

  Ref<vm::Cell> out_msg_env;
  Ref<vm::Cell> reimport;
  bool tr_req = false;

  // continue checking inbound message
  switch (tag) {
    case block::gen::InMsg::msg_import_imm: {
      // Optimized immediate message handling
      if (cur_prefix != dest_prefix || !shard_contains(shard_, src_prefix)) {
        return reject_query("Invalid address prefix or shard mismatch");
      }
      
      if (transaction.is_null()) {
        return reject_query("Missing transaction for immediate message");
      }
      
      block::gen::OutMsg::Record_msg_export_imm out_msg;
      auto out_msg_cs = out_msg_dict_->lookup(key, 256);
      
      if (!is_special_in_msg(*in_msg)) {
        if (!tlb::csr_unpack_safe(out_msg_cs, out_msg)) {
          return reject_query("Missing or invalid OutMsg for immediate message");
        }
        out_msg_env = std::move(out_msg.out_msg);
        reimport = std::move(out_msg.reimport);
      }
      
      if (*fwd_fee != *env.fwd_fee_remaining) {
        return reject_query("Forward fee mismatch for immediate message");
      }
      break;
    }
    case block::gen::InMsg::msg_import_fin: {
      // msg_import_fin$100 in_msg:^MsgEnvelope transaction:^Transaction fwd_fee:Grams
      // msg_import_deferred_fin$00100 in_msg:^MsgEnvelope transaction:^Transaction fwd_fee:Grams
      // importing and processing an internal message with destination in this shard
      CHECK(transaction.not_null());
      CHECK(shard_contains(shard_, next_prefix));
      if (shard_contains(shard_, cur_prefix)) {
        // we imported this message from our shard!
        block::gen::OutMsg::Record_msg_export_deq_imm out_msg;
        if (!tlb::csr_unpack_safe(out_msg_dict_->lookup(key, 256), out_msg)) {
          return reject_query("inbound internal message with hash "s + key.to_hex(256) +
                              " is a msg_import_fin$100 with current address " + cur_prefix.to_str() +
                              "... already in our shard, but the corresponding OutMsg does not exist, or is not a "
                              "valid msg_export_deq_imm$100");
        }
        out_msg_env = std::move(out_msg.out_msg);
        reimport = std::move(out_msg.reimport);
      } else {
        CHECK(cur_prefix != next_prefix);
        // check that the message was present in the output queue of a neighbor, and that it has not been processed before
        if (!check_imported_message(msg_env)) {
          return false;
        }
      }
      // ...
      // fwd_fee must be equal to the fwd_fee_remaining of this MsgEnvelope
      if (*fwd_fee != *env.fwd_fee_remaining) {
        return reject_query("msg_import_imm$011 InMsg with hash "s + key.to_hex(256) +
                            " is invalid because its collected fwd_fee=" + td::dec_string(fwd_fee) +
                            " is not equal to fwd_fee_remaining=" + td::dec_string(env.fwd_fee_remaining) +
                            " of this message (envelope)");
      }
      // ...
      break;
    }
    case block::gen::InMsg::msg_import_deferred_fin: {
      // fwd_fee must be equal to the fwd_fee_remaining of this MsgEnvelope
      if (*fwd_fee != *env.fwd_fee_remaining) {
        return reject_query("msg_import_imm$011 InMsg with hash "s + key.to_hex(256) +
                            " is invalid because its collected fwd_fee=" + td::dec_string(fwd_fee) +
                            " is not equal to fwd_fee_remaining=" + td::dec_string(env.fwd_fee_remaining) +
                            " of this message (envelope)");
      }
      // ...
      break;
    }
    case block::gen::InMsg::msg_import_deferred_tr:
    case block::gen::InMsg::msg_import_tr: {
      // msg_import_tr$101 in_msg:^MsgEnvelope out_msg:^MsgEnvelope transit_fee:Grams
      // msg_import_deferred_tr$00101 in_msg:^MsgEnvelope out_msg:^MsgEnvelope
      // importing and relaying a (transit) internal message with destination outside this shard
      if (cur_prefix == dest_prefix && tag == block::gen::InMsg::msg_import_tr) {
        return reject_query("inbound internal message with hash "s + key.to_hex(256) +
                            " is a msg_import_tr$101 (a transit message), but its current address " +
                            cur_prefix.to_str() + " is already equal to its final destination");
      }
      if (cur_prefix != next_prefix && tag == block::gen::InMsg::msg_import_deferred_tr) {
        return reject_query("internal message from DispatchQueue with hash "s + key.to_hex(256) +
                            " is a msg_import_deferred_tr$00101, but its current address " + cur_prefix.to_str() +
                            " is not equal to next address");
      }
      CHECK(transaction.is_null());
      auto out_msg_cs = out_msg_dict_->lookup(key, 256);
      if (out_msg_cs.is_null()) {
        return reject_query("inbound internal message with hash "s + key.to_hex(256) +
                            " is a msg_import_tr$101 (transit message), but the corresponding OutMsg does not exist");
      }
      if (shard_contains(shard_, cur_prefix) && tag == block::gen::InMsg::msg_import_tr) {
        // we imported this message from our shard!
        // (very rare situation possible only after merge)
        tr_req = true;
        block::gen::OutMsg::Record_msg_export_tr_req out_msg;
        if (!tlb::csr_unpack_safe(out_msg_cs, out_msg)) {
          return reject_query(
              "inbound internal message with hash "s + key.to_hex(256) +
              " is a msg_import_tr$101 (transit message) with current address " + cur_prefix.to_str() +
              "... already in our shard, but the corresponding OutMsg is not a valid msg_export_tr_req$111");
        }
        out_msg_env = std::move(out_msg.out_msg);
        reimport = std::move(out_msg.imported);
      } else if (tag == block::gen::InMsg::msg_import_tr) {
        block::gen::OutMsg::Record_msg_export_tr out_msg;
        if (!tlb::csr_unpack_safe(out_msg_cs, out_msg)) {
          return reject_query(
              "inbound internal message with hash "s + key.to_hex(256) +
              " is a msg_import_tr$101 (transit message) with current address " + cur_prefix.to_str() +
              "... outside of our shard, but the corresponding OutMsg is not a valid msg_export_tr$011");
        }
        out_msg_env = std::move(out_msg.out_msg);
        reimport = std::move(out_msg.imported);
        // check that the message was present in the output queue of a neighbor, and that it has not been processed before
        if (!check_imported_message(msg_env)) {
          return false;
        }
      } else {
        block::gen::OutMsg::Record_msg_export_deferred_tr out_msg;
        if (!tlb::csr_unpack_safe(out_msg_cs, out_msg)) {
          return reject_query(
              "inbound internal message with hash "s + key.to_hex(256) +
              " is a msg_import_deferred_tr$00101 with current address " + cur_prefix.to_str() +
              "... outside of our shard, but the corresponding OutMsg is not a valid msg_export_deferred_tr$10101");
        }
        out_msg_env = std::move(out_msg.out_msg);
        reimport = std::move(out_msg.imported);
      }
      // perform hypercube routing for this transit message
      auto route_info = block::perform_hypercube_routing(next_prefix, dest_prefix, shard_);
      if ((unsigned)route_info.first > 96 || (unsigned)route_info.second > 96) {
        return reject_query("cannot perform (check) hypercube routing for transit inbound message with hash "s +
                            key.to_hex(256) + ": src=" + src_prefix.to_str() + " cur=" + cur_prefix.to_str() +
                            " next=" + next_prefix.to_str() + " dest=" + dest_prefix.to_str() + "; our shard is " +
                            shard_.to_str());
      }
      auto new_cur_prefix = block::interpolate_addr(next_prefix, dest_prefix, route_info.first);
      auto new_next_prefix = block::interpolate_addr(next_prefix, dest_prefix, route_info.second);
      // unpack out_msg:^MsgEnvelope from msg_import_tr
      block::tlb::MsgEnvelope::Record_std tr_env;
      if (!tlb::unpack_cell(tr_msg_env, tr_env)) {
        return reject_query("InMsg for transit message with hash "s + key.to_hex(256) +
                            " refers to an invalid rewritten message envelope");
      }
      // the rewritten transit message envelope must contain the same message
      if (tr_env.msg->get_hash() != msg->get_hash()) {
        return reject_query("InMsg for transit message with hash "s + key.to_hex(256) +
                            " refers to a rewritten message envelope containing another message");
      }
      // check that the message has been routed according to hypercube routing
      auto tr_cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, tr_env.cur_addr);
      auto tr_next_prefix = block::interpolate_addr(src_prefix, dest_prefix, tr_env.next_addr);
      if (tr_cur_prefix != new_cur_prefix || tr_next_prefix != new_next_prefix) {
        return reject_query("InMsg for transit message with hash "s + key.to_hex(256) +
                            " tells us that it has been adjusted to current address " + tr_cur_prefix.to_str() +
                            "... and hext hop address " + tr_next_prefix.to_str() +
                            " while the correct values dictated by hypercube routing are " + new_cur_prefix.to_str() +
                            "... and " + new_next_prefix.to_str() + "...");
      }
      // check that the collected transit fee with new fwd_fee_remaining equal the original fwd_fee_remaining
      // (correctness of fwd_fee itself will be checked later)
      if (tr_env.fwd_fee_remaining > orig_fwd_fee || *(tr_env.fwd_fee_remaining + fwd_fee) != *env.fwd_fee_remaining) {
        return reject_query("InMsg for transit message with hash "s + key.to_hex(256) + " declares transit fees of " +
                            td::dec_string(fwd_fee) + ", but fwd_fees_remaining has decreased from " +
                            td::dec_string(env.fwd_fee_remaining) + " to " + td::dec_string(tr_env.fwd_fee_remaining) +
                            " in transit");
      }
      if (tr_env.metadata != env.metadata) {
        return reject_query(
            PSTRING() << "InMsg for transit message with hash " << key.to_hex(256) << " contains invalid MsgMetadata: "
                      << (env.metadata ? env.metadata.value().to_str() : "<none>") << " in in_msg, but "
                      << (tr_env.metadata ? tr_env.metadata.value().to_str() : "<none>") << " in out_msg");
      }
      if (tr_env.emitted_lt != env.emitted_lt) {
        return reject_query(
            PSTRING() << "InMsg for transit message with hash " << key.to_hex(256) << " contains invalid emitted_lt: "
                      << (env.emitted_lt ? td::to_string(env.emitted_lt.value()) : "<none>") << " in in_msg, but "
                      << (tr_env.emitted_lt ? td::to_string(tr_env.emitted_lt.value()) : "<none>") << " in out_msg");
      }
      if (tr_msg_env->get_hash() != out_msg_env->get_hash()) {
        return reject_query(
            "InMsg for transit message with hash "s + key.to_hex(256) +
            " contains rewritten MsgEnvelope different from that stored in corresponding OutMsgDescr (" +
            (tr_req ? "requeued" : "usual") + "transit)");
      }
      // check the amount of the transit fee
      td::RefInt256 transit_fee =
          from_dispatch_queue ? td::zero_refint() : action_phase_cfg_.fwd_std.get_next_part(env.fwd_fee_remaining);
      if (*transit_fee != *fwd_fee) {
        return reject_query("InMsg for transit message with hash "s + key.to_hex(256) +
                            " declared collected transit fees to be " + td::dec_string(fwd_fee) +
                            " (deducted from the remaining forwarding fees of " +
                            td::dec_string(env.fwd_fee_remaining) +
                            "), but we have computed another value of transit fees " + td::dec_string(transit_fee));
      }
      break;
    }
    default:
      return fatal_error(PSTRING() << "unknown InMsgTag " << tag);
  }

  if (reimport.not_null()) {
    // transit message: msg_export_tr + msg_import_tr
    // or message re-imported from this very shard
    // either msg_export_imm + msg_import_imm
    // or msg_export_deq_imm + msg_import_fin
    // or msg_export_tr_req + msg_import_tr (rarely, only after merge)
    // must have a corresponding OutMsg record
    if (!in_msg->contents_equal(vm::load_cell_slice(std::move(reimport)))) {
      return reject_query("OutMsg corresponding to reimport InMsg with hash "s + key.to_hex(256) +
                          " refers to a different reimport InMsg");
    }
    // for transit messages, OutMsg refers to the newly-created outbound messages (not to the re-imported old outbound message)
    if (tag != block::gen::InMsg::msg_import_tr && tag != block::gen::InMsg::msg_import_deferred_tr &&
        out_msg_env->get_hash() != msg_env->get_hash()) {
      return reject_query(
          "InMsg with hash "s + key.to_hex(256) +
          " is a reimport record, but the corresponding OutMsg exports a MsgEnvelope with a different hash");
    }
  }
  return true;
}

}  // namespace solution
