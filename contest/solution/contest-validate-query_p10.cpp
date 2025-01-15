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
 * Check that the difference between the old and new dispatch queues is reflected in OutMsgs and InMsgs
 *
 * @returns True if the check is successful, false otherwise.
 */
bool ContestValidateQuery::check_dispatch_queue_update() {
  if (!new_dispatch_queue_messages_.empty()) {
    auto it = new_dispatch_queue_messages_.begin();
    return reject_query(PSTRING() << "DispatchQueue has a new message with src_addr=" << it->first.first.to_hex()
                                  << ", lt=" << it->first.second << ", but no correseponding OutMsg exists");
  }
  if (!removed_dispatch_queue_messages_.empty()) {
    auto it = removed_dispatch_queue_messages_.begin();
    return reject_query(PSTRING() << "message with src_addr=" << it->first.first.to_hex() << ", lt=" << it->first.second
                                  << " was removed from DispatchQueue, but no correseponding InMsg exists");
  }
  return true;
}

/**
 * Checks the validity of an outbound message in the neighbor's queue.
 * Similar to Collator::process_inbound_message.
 *
 * @param enq_msg The enqueued message to validate.
 * @param lt The logical time of the message.
 * @param key The 32+64+256-bit key of the message.
 * @param nb The neighbor's description.
 * @param unprocessed A boolean flag that will be set to true if the message is unprocessed, false otherwise.
 *
 * @returns True if the message is valid, false otherwise.
 */
bool ContestValidateQuery::check_neighbor_outbound_message(Ref<vm::CellSlice> enq_msg, ton::LogicalTime lt,
                                                           td::ConstBitPtr key, const block::McShardDescr& nb,
                                                           bool& unprocessed, bool& processed_here,
                                                           td::Bits256& msg_hash) {
  unprocessed = false;
  block::EnqueuedMsgDescr enq;
  if (!enq.unpack(enq_msg.write())) {  // unpack EnqueuedMsg
    return reject_query("cannot unpack EnqueuedMsg with key "s + key.to_hex(352) +
                        " in outbound queue of our neighbor " + nb.blk_.to_str());
  }
  if (!enq.check_key(key)) {  // check key
    return reject_query("EnqueuedMsg with key "s + key.to_hex(352) + " in outbound queue of our neighbor " +
                        nb.blk_.to_str() + " has incorrect key for its contents and envelope");
  }
  if (enq.lt_ != lt) {
    return reject_query(PSTRING() << "EnqueuedMsg with key " << key.to_hex(352) << " in outbound queue of our neighbor "
                                  << nb.blk_.to_str() << " pretends to have been created at lt " << lt
                                  << " but its actual creation lt is " << enq.lt_);
  }
  CHECK(shard_contains(shard_, enq.next_prefix_));
  auto in_entry = in_msg_dict_->lookup(key + 96, 256);
  auto out_entry = out_msg_dict_->lookup(key + 96, 256);
  bool f0 = ps_.processed_upto_->already_processed(enq);
  bool f1 = ns_.processed_upto_->already_processed(enq);
  processed_here = f1 && !f0;
  msg_hash = enq.hash_;
  if (f0 && !f1) {
    return fatal_error(
        "a previously processed message has been un-processed (impossible situation after the validation of "
        "ProcessedInfo)");
  }
  if (f0) {
    // this message has been processed in a previous block of this shard
    // just check that we have not imported it once again
    if (in_entry.not_null()) {
      return reject_query("have an InMsg entry for processing again already processed EnqueuedMsg with key "s +
                          key.to_hex(352) + " of neighbor " + nb.blk_.to_str());
    }
    if (shard_contains(shard_, enq.cur_prefix_)) {
      // if this message comes from our own outbound queue, we must have dequeued it
      if (out_entry.is_null()) {
        return reject_query("our old outbound queue contains EnqueuedMsg with key "s + key.to_hex(352) +
                            " already processed by this shard, but there is no ext_message_deq OutMsg record for this "
                            "message in this block");
      }
      int tag = block::gen::t_OutMsg.get_tag(*out_entry);
      if (tag == block::gen::OutMsg::msg_export_deq_short) {
        block::gen::OutMsg::Record_msg_export_deq_short deq;
        if (!tlb::csr_unpack(std::move(out_entry), deq)) {
          return reject_query(
              "cannot unpack msg_export_deq_short OutMsg record for already processed EnqueuedMsg with key "s +
              key.to_hex(352) + " of old outbound queue");
        }
        if (deq.msg_env_hash != enq.msg_env_->get_hash().bits()) {
          return reject_query("unpack ext_message_deq OutMsg record for already processed EnqueuedMsg with key "s +
                              key.to_hex(352) + " of old outbound queue refers to MsgEnvelope with different hash " +
                              deq.msg_env_hash.to_hex());
        }
      } else {
        block::gen::OutMsg::Record_msg_export_deq deq;
        if (!tlb::csr_unpack(std::move(out_entry), deq)) {
          return reject_query(
              "cannot unpack msg_export_deq OutMsg record for already processed EnqueuedMsg with key "s +
              key.to_hex(352) + " of old outbound queue");
        }
        if (deq.out_msg->get_hash() != enq.msg_env_->get_hash()) {
          return reject_query("unpack ext_message_deq OutMsg record for already processed EnqueuedMsg with key "s +
                              key.to_hex(352) + " of old outbound queue contains a different MsgEnvelope");
        }
      }
    }
    // next check is incorrect after a merge, when ns_.processed_upto has > 1 entries
    // we effectively comment it out
    return true;
    // NB. we might have a non-trivial dequeueing out_entry with this message hash, but another envelope (for transit messages)
    // (so we cannot assert that out_entry is null)
    if (claimed_proc_lt_ && (claimed_proc_lt_ < lt || (claimed_proc_lt_ == lt && claimed_proc_hash_ < enq.hash_))) {
      LOG(INFO) << "old processed_upto: " << ps_.processed_upto_->to_str();
      LOG(INFO) << "new processed_upto: " << ns_.processed_upto_->to_str();
      return fatal_error(
          -669, PSTRING() << "internal inconsistency: new ProcessedInfo claims to have processed all messages up to ("
                          << claimed_proc_lt_ << "," << claimed_proc_hash_.to_hex()
                          << "), but we had somehow already processed a message (" << lt << "," << enq.hash_.to_hex()
                          << ") from OutMsgQueue of neighbor " << nb.blk_.to_str() << " key " << key.to_hex(352));
    }
    return true;
  }
  if (f1) {
    // this message must have been imported and processed in this very block
    // (because it is marked processed after this block, but not before)
    if (!claimed_proc_lt_ || claimed_proc_lt_ < lt || (claimed_proc_lt_ == lt && claimed_proc_hash_ < enq.hash_)) {
      return fatal_error(
          -669, PSTRING() << "internal inconsistency: new ProcessedInfo claims to have processed all messages up to ("
                          << claimed_proc_lt_ << "," << claimed_proc_hash_.to_hex()
                          << "), but we had somehow processed in this block a message (" << lt << ","
                          << enq.hash_.to_hex() << ") from OutMsgQueue of neighbor " << nb.blk_.to_str() << " key "
                          << key.to_hex(352));
    }
    // must have a msg_import_fin or msg_import_tr InMsg record
    if (in_entry.is_null()) {
      return reject_query("there is no InMsg entry for processing EnqueuedMsg with key "s + key.to_hex(352) +
                          " of neighbor " + nb.blk_.to_str() +
                          " which is claimed to be processed by new ProcessedInfo of this block");
    }
    int tag = block::gen::t_InMsg.get_tag(*in_entry);
    if (tag != block::gen::InMsg::msg_import_fin && tag != block::gen::InMsg::msg_import_tr) {
      return reject_query(
          "expected either a msg_import_fin or a msg_import_tr InMsg record for processing EnqueuedMsg with key "s +
          key.to_hex(352) + " of neighbor " + nb.blk_.to_str() +
          " which is claimed to be processed by new ProcessedInfo of this block");
    }
    if (in_entry->prefetch_ref()->get_hash() != enq.msg_env_->get_hash()) {
      return reject_query("InMsg record for processing EnqueuedMsg with key "s + key.to_hex(352) + " of neighbor " +
                          nb.blk_.to_str() +
                          " which is claimed to be processed by new ProcessedInfo of this block contains a reference "
                          "to a different MsgEnvelope");
    }
    // all other checks have been done while checking InMsgDescr
    return true;
  }
  unprocessed = true;
  // the message is left unprocessed in our virtual "inbound queue"
  // just a simple sanity check
  if (claimed_proc_lt_ && !(claimed_proc_lt_ < lt || (claimed_proc_lt_ == lt && claimed_proc_hash_ < enq.hash_))) {
    return fatal_error(
        -669, PSTRING() << "internal inconsistency: new ProcessedInfo claims to have processed all messages up to ("
                        << claimed_proc_lt_ << "," << claimed_proc_hash_.to_hex()
                        << "), but we somehow have not processed a message (" << lt << "," << enq.hash_.to_hex()
                        << ") from OutMsgQueue of neighbor " << nb.blk_.to_str() << " key " << key.to_hex(352));
  }
  return true;
}

/**
 * Checks messages from the outbound queues of the neighbors.
 *
 * @returns True if the messages are valid, false otherwise.
 */
bool ContestValidateQuery::check_in_queue() {
  int imported_messages_count = 0;
  in_msg_dict_->check_for_each_extra([&](Ref<vm::CellSlice> value, Ref<vm::CellSlice>, td::ConstBitPtr, int) {
    int tag = block::gen::t_InMsg.get_tag(*value);
    if (tag == block::gen::InMsg::msg_import_fin || tag == block::gen::InMsg::msg_import_tr) {
      ++imported_messages_count;
    }
    return true;
  });
  if (imported_messages_count == 0 && claimed_proc_lt_ == 0) {
    return true;
  }

  std::vector<block::OutputQueueMerger::Neighbor> neighbor_queues;
  for (const auto& descr : neighbors_) {
    td::BitArray<96> key;
    key.bits().store_int(descr.workchain(), 32);
    (key.bits() + 32).store_uint(descr.shard().shard, 64);
    neighbor_queues.emplace_back(descr.top_block_id(), descr.outmsg_root, descr.disabled_);
  }
  block::OutputQueueMerger nb_out_msgs(shard_, std::move(neighbor_queues));
  while (!nb_out_msgs.is_eof()) {
    auto kv = nb_out_msgs.extract_cur();
    CHECK(kv && kv->msg.not_null());
    LOG(DEBUG) << "processing inbound message with (lt,hash)=(" << kv->lt << "," << kv->key.to_hex()
               << ") from neighbor #" << kv->source;
    if (verbosity > 3) {
      std::cerr << "inbound message: lt=" << kv->lt << " from=" << kv->source << " key=" << kv->key.to_hex() << " msg=";
      block::gen::t_EnqueuedMsg.print(std::cerr, *(kv->msg));
    }
    bool unprocessed = false;
    bool processed_here = false;
    td::Bits256 msg_hash;
    if (!check_neighbor_outbound_message(kv->msg, kv->lt, kv->key.cbits(), neighbors_.at(kv->source), unprocessed,
                                         processed_here, msg_hash)) {
      if (verbosity > 1) {
        std::cerr << "invalid neighbor outbound message: lt=" << kv->lt << " from=" << kv->source
                  << " key=" << kv->key.to_hex() << " msg=";
        block::gen::t_EnqueuedMsg.print(std::cerr, *(kv->msg));
      }
      return reject_query("error processing outbound internal message "s + kv->key.to_hex() + " of neighbor " +
                          neighbors_.at(kv->source).blk_.to_str());
    }
    if (processed_here) {
      --imported_messages_count;
    }
    auto msg_lt = kv->lt;
    if (imported_messages_count == 0 && msg_lt == claimed_proc_lt_ && msg_hash == claimed_proc_hash_) {
      return true;
    }
    if (unprocessed) {
      return true;
    }
    nb_out_msgs.next();
  }
  return true;
}

/**
 * Creates a new Account object from the given address and serialized account data.
 * Creates a new Account if not found.
 * Similar to Collator::make_account_from()
 *
 * @param addr A pointer to the 256-bit address of the account.
 * @param account A cell slice with an account serialized using ShardAccount TLB-scheme.
 *
 * @returns A unique pointer to the created Account object, or nullptr if the creation failed.
 */
std::unique_ptr<block::Account> ContestValidateQuery::make_account_from(td::ConstBitPtr addr,
                                                                        Ref<vm::CellSlice> account) {
  auto ptr = std::make_unique<block::Account>(workchain(), addr);
  if (account.is_null()) {
    if (!ptr->init_new(now_)) {
      return nullptr;
    }
  } else if (!ptr->unpack(std::move(account), now_, false)) {
    return nullptr;
  }
  ptr->block_lt = start_lt_;
  return ptr;
}

/**
 * Retreives an Account object from the data in the shard state.
 * Accounts are cached in the ValidatorQuery's map.
 * Similar to Collator::make_account()
 *
 * @param addr The 256-bit address of the account.
 *
 * @returns Pointer to the account if found or created successfully.
 *          Returns nullptr if an error occured.
 */
std::unique_ptr<block::Account> ContestValidateQuery::unpack_account(td::ConstBitPtr addr) {
  auto dict_entry = ps_.account_dict_->lookup_extra(addr, 256);
  auto new_acc = make_account_from(addr, std::move(dict_entry.first));
  if (!new_acc) {
    reject_query("cannot load state of account "s + addr.to_hex(256) + " from previous shardchain state");
    return {};
  }
  if (!new_acc->belongs_to_shard(shard_)) {
    reject_query(PSTRING() << "old state of account " << addr.to_hex(256)
                           << " does not really belong to current shard");
    return {};
  }
  return new_acc;
}

/**
 * Checks the validity of a single transaction for a given account.
 * Performs transaction execution.
 *
 * @param account The account of the transaction.
 * @param lt The logical time of the transaction.
 * @param trans_root The root of the transaction.
 * @param is_first Flag indicating if this is the first transaction of the account.
 * @param is_last Flag indicating if this is the last transaction of the account.
 *
 * @returns True if the transaction is valid, false otherwise.
 */
bool ContestValidateQuery::check_one_transaction(block::Account& account, ton::LogicalTime lt, Ref<vm::Cell> trans_root,
                                                 bool is_first, bool is_last) {
  LOG(DEBUG) << "checking transaction " << lt << " of account " << account.addr.to_hex();
  const StdSmcAddress& addr = account.addr;
  block::gen::Transaction::Record trans;
  block::gen::HASH_UPDATE::Record hash_upd;
  CHECK(tlb::unpack_cell(trans_root, trans) &&
        tlb::type_unpack_cell(std::move(trans.state_update), block::gen::t_HASH_UPDATE_Account, hash_upd));
  auto in_msg_root = trans.r1.in_msg->prefetch_ref();
  bool external{false}, ihr_delivered{false}, need_credit_phase{false};
  // check input message
  block::CurrencyCollection money_imported(0), money_exported(0);
  bool is_special_tx = false;  // recover/mint transaction
  auto td_cs = vm::load_cell_slice(trans.description);
  int tag = block::gen::t_TransactionDescr.get_tag(td_cs);
  CHECK(tag >= 0);  // we have already validated the serialization of all Transactions
  td::optional<block::MsgMetadata> in_msg_metadata;
  if (in_msg_root.not_null()) {
    auto in_descr_cs = in_msg_dict_->lookup(in_msg_root->get_hash().as_bitslice());
    if (in_descr_cs.is_null()) {
      return reject_query(PSTRING() << "inbound message with hash " << in_msg_root->get_hash().to_hex()
                                    << " of transaction " << lt << " of account " << addr.to_hex()
                                    << " does not have a corresponding InMsg record");
    }
    auto in_msg_tag = block::gen::t_InMsg.get_tag(*in_descr_cs);
    if (in_msg_tag != block::gen::InMsg::msg_import_ext && in_msg_tag != block::gen::InMsg::msg_import_fin &&
        in_msg_tag != block::gen::InMsg::msg_import_imm && in_msg_tag != block::gen::InMsg::msg_import_ihr &&
        in_msg_tag != block::gen::InMsg::msg_import_deferred_fin) {
      return reject_query(PSTRING() << "inbound message with hash " << in_msg_root->get_hash().to_hex()
                                    << " of transaction " << lt << " of account " << addr.to_hex()
                                    << " has an invalid InMsg record (not one of msg_import_ext, msg_import_fin, "
                                       "msg_import_imm, msg_import_ihr or msg_import_deferred_fin)");
    }
    is_special_tx = is_special_in_msg(*in_descr_cs);
    // once we know there is a InMsg with correct hash, we already know that it contains a message with this hash (by the verification of InMsg), so it is our message
    // have still to check its destination address and imported value
    // and that it refers to this transaction
    Ref<vm::CellSlice> dest;
    if (in_msg_tag == block::gen::InMsg::msg_import_ext) {
      block::gen::CommonMsgInfo::Record_ext_in_msg_info info;
      CHECK(tlb::unpack_cell_inexact(in_msg_root, info));
      dest = std::move(info.dest);
      external = true;
    } else {
      block::gen::CommonMsgInfo::Record_int_msg_info info;
      CHECK(tlb::unpack_cell_inexact(in_msg_root, info));
      if (info.created_lt >= lt) {
        return reject_query(PSTRING() << "transaction " << lt << " of " << addr.to_hex()
                                      << " processed inbound message created later at logical time "
                                      << info.created_lt);
      }
      LogicalTime emitted_lt = info.created_lt;  // See ContestValidateQuery::check_message_processing_order
      if (in_msg_tag == block::gen::InMsg::msg_import_imm || in_msg_tag == block::gen::InMsg::msg_import_fin ||
          in_msg_tag == block::gen::InMsg::msg_import_deferred_fin) {
        block::tlb::MsgEnvelope::Record_std msg_env;
        if (!block::tlb::unpack_cell(in_descr_cs->prefetch_ref(), msg_env)) {
          return reject_query(PSTRING() << "InMsg record for inbound message with hash "
                                        << in_msg_root->get_hash().to_hex() << " of transaction " << lt
                                        << " of account " << addr.to_hex() << " does not have a valid MsgEnvelope");
        }
        in_msg_metadata = std::move(msg_env.metadata);
        if (msg_env.emitted_lt) {
          emitted_lt = msg_env.emitted_lt.value();
        }
      }
      if (info.created_lt != start_lt_ || !is_special_tx) {
        msg_proc_lt_.emplace_back(addr, lt, emitted_lt);
      }
      dest = std::move(info.dest);
      CHECK(money_imported.validate_unpack(info.value));
      ihr_delivered = (in_msg_tag == block::gen::InMsg::msg_import_ihr);
      if (!ihr_delivered) {
        money_imported += block::tlb::t_Grams.as_integer(info.ihr_fee);
      }
      CHECK(money_imported.is_valid());
    }
    WorkchainId d_wc;
    StdSmcAddress d_addr;
    CHECK(block::tlb::t_MsgAddressInt.extract_std_address(dest, d_wc, d_addr));
    if (d_wc != workchain() || d_addr != addr) {
      return reject_query(PSTRING() << "inbound message of transaction " << lt << " of account " << addr.to_hex()
                                    << " has a different destination address " << d_wc << ":" << d_addr.to_hex());
    }
    auto in_msg_trans = in_descr_cs->prefetch_ref(1);  // trans:^Transaction
    CHECK(in_msg_trans.not_null());
    if (in_msg_trans->get_hash() != trans_root->get_hash()) {
      return reject_query(PSTRING() << "InMsg record for inbound message with hash " << in_msg_root->get_hash().to_hex()
                                    << " of transaction " << lt << " of account " << addr.to_hex()
                                    << " refers to a different processing transaction");
    }
  }
  // check output messages
  td::optional<block::MsgMetadata> new_msg_metadata;
  if (msg_metadata_enabled_) {
    if (external || is_special_tx || tag != block::gen::TransactionDescr::trans_ord) {
      new_msg_metadata = block::MsgMetadata{0, account.workchain, account.addr, (LogicalTime)trans.lt};
    } else if (in_msg_metadata) {
      new_msg_metadata = std::move(in_msg_metadata);
      ++new_msg_metadata.value().depth;
    }
  }
  vm::Dictionary out_dict{trans.r1.out_msgs, 15};
  for (int i = 0; i < trans.outmsg_cnt; i++) {
    auto out_msg_root = out_dict.lookup_ref(td::BitArray<15>{i});
    CHECK(out_msg_root.not_null());  // we have pre-checked this
    auto out_descr_cs = out_msg_dict_->lookup(out_msg_root->get_hash().as_bitslice());
    if (out_descr_cs.is_null()) {
      return reject_query(PSTRING() << "outbound message #" << i + 1 << " with hash "
                                    << out_msg_root->get_hash().to_hex() << " of transaction " << lt << " of account "
                                    << addr.to_hex() << " does not have a corresponding OutMsg record");
    }
    auto tag = block::gen::t_OutMsg.get_tag(*out_descr_cs);
    if (tag != block::gen::OutMsg::msg_export_ext && tag != block::gen::OutMsg::msg_export_new &&
        tag != block::gen::OutMsg::msg_export_imm && tag != block::gen::OutMsg::msg_export_new_defer) {
      return reject_query(PSTRING() << "outbound message #" << i + 1 << " with hash "
                                    << out_msg_root->get_hash().to_hex() << " of transaction " << lt << " of account "
                                    << addr.to_hex()
                                    << " has an invalid OutMsg record (not one of msg_export_ext, msg_export_new, "
                                       "msg_export_imm or msg_export_new_defer)");
    }
    // once we know there is an OutMsg with correct hash, we already know that it contains a message with this hash
    // (by the verification of OutMsg), so it is our message
    // have still to check its source address, lt and imported value
    // and that it refers to this transaction as its origin
    Ref<vm::CellSlice> src;
    LogicalTime message_lt;
    if (tag == block::gen::OutMsg::msg_export_ext) {
      block::gen::CommonMsgInfo::Record_ext_out_msg_info info;
      CHECK(tlb::unpack_cell_inexact(out_msg_root, info));
      src = std::move(info.src);
      message_lt = info.created_lt;
    } else {
      block::gen::CommonMsgInfo::Record_int_msg_info info;
      CHECK(tlb::unpack_cell_inexact(out_msg_root, info));
      src = std::move(info.src);
      message_lt = info.created_lt;
      block::tlb::MsgEnvelope::Record_std msg_env;
      CHECK(tlb::unpack_cell(out_descr_cs->prefetch_ref(), msg_env));
      // unpack exported message value (from this transaction)
      block::CurrencyCollection msg_export_value;
      CHECK(msg_export_value.unpack(info.value));
      msg_export_value += block::tlb::t_Grams.as_integer(info.ihr_fee);
      msg_export_value += msg_env.fwd_fee_remaining;
      CHECK(msg_export_value.is_valid());
      money_exported += msg_export_value;
      if (msg_env.metadata != new_msg_metadata) {
        return reject_query(PSTRING() << "outbound message #" << i + 1 << " with hash "
                                      << out_msg_root->get_hash().to_hex() << " of transaction " << lt << " of account "
                                      << addr.to_hex() << " has invalid metadata in an OutMsg record: expected "
                                      << (new_msg_metadata ? new_msg_metadata.value().to_str() : "<none>") << ", found "
                                      << (msg_env.metadata ? msg_env.metadata.value().to_str() : "<none>"));
      }
    }
    WorkchainId s_wc;
    StdSmcAddress ss_addr;  // s_addr is some macros in Windows
    CHECK(block::tlb::t_MsgAddressInt.extract_std_address(src, s_wc, ss_addr));
    if (s_wc != workchain() || ss_addr != addr) {
      return reject_query(PSTRING() << "outbound message #" << i + 1 << " of transaction " << lt << " of account "
                                    << addr.to_hex() << " has a different source address " << s_wc << ":"
                                    << ss_addr.to_hex());
    }
    auto out_msg_trans = out_descr_cs->prefetch_ref(1);  // trans:^Transaction
    CHECK(out_msg_trans.not_null());
    if (out_msg_trans->get_hash() != trans_root->get_hash()) {
      return reject_query(PSTRING() << "OutMsg record for outbound message #" << i + 1 << " with hash "
                                    << out_msg_root->get_hash().to_hex() << " of transaction " << lt << " of account "
                                    << addr.to_hex() << " refers to a different processing transaction");
    }
    if (tag != block::gen::OutMsg::msg_export_ext) {
      bool is_deferred = tag == block::gen::OutMsg::msg_export_new_defer;
      if (account_expected_defer_all_messages_.count(ss_addr) && !is_deferred) {
        return reject_query(
            PSTRING() << "outbound message #" << i + 1 << " on account " << workchain() << ":" << ss_addr.to_hex()
                      << " must be deferred because this account has earlier messages in DispatchQueue");
      }
      if (is_deferred) {
        LOG(INFO) << "message from account " << workchain() << ":" << ss_addr.to_hex() << " with lt " << message_lt
                  << " was deferred";
        if (!deferring_messages_enabled_ && !account_expected_defer_all_messages_.count(ss_addr)) {
          return reject_query(PSTRING() << "outbound message #" << i + 1 << " on account " << workchain() << ":"
                                        << ss_addr.to_hex() << " is deferred, but deferring messages is disabled");
        }
        if (i == 0 && !account_expected_defer_all_messages_.count(ss_addr)) {
          return reject_query(PSTRING() << "outbound message #1 on account " << workchain() << ":" << ss_addr.to_hex()
                                        << " must not be deferred (the first message cannot be deferred unless some "
                                           "prevoius messages are deferred)");
        }
        account_expected_defer_all_messages_.insert(ss_addr);
      }
    }
  }
  CHECK(money_exported.is_valid());
  // check general transaction data
  block::CurrencyCollection old_balance{account.get_balance()};
  if (tag == block::gen::TransactionDescr::trans_merge_prepare ||
      tag == block::gen::TransactionDescr::trans_merge_install ||
      tag == block::gen::TransactionDescr::trans_split_prepare ||
      tag == block::gen::TransactionDescr::trans_split_install) {
    bool split = (tag == block::gen::TransactionDescr::trans_split_prepare ||
                  tag == block::gen::TransactionDescr::trans_split_install);
    if (split && !before_split_) {
      return reject_query(PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                                    << " is a split prepare/install transaction, but this block is not before a split");
    }
    if (split && !is_last) {
      return reject_query(PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                                    << " is a split prepare/install transaction, but it is not the last transaction "
                                       "for this account in this block");
    }
    if (!split && !after_merge_) {
      return reject_query(
          PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                    << " is a merge prepare/install transaction, but this block is not immediately after a merge");
    }
    if (!split && !is_first) {
      return reject_query(PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                                    << " is a merge prepare/install transaction, but it is not the first transaction "
                                       "for this account in this block");
    }
    // check later a global configuration flag in config_.global_flags_
    // (for now, split/merge transactions are always globally disabled)
    return reject_query(PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                                  << " is a split/merge prepare/install transaction, which are globally disabled");
  }
  if (tag == block::gen::TransactionDescr::trans_tick_tock) {
    return reject_query(PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                                  << " is a tick-tock transaction, which is impossible outside a masterchain block");
  }
  if (tag == block::gen::TransactionDescr::trans_storage && !is_first) {
    return reject_query(
        PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                  << " is a storage transaction, but it is not the first transaction for this account in this block");
  }
  // check that the original account state has correct hash
  CHECK(account.total_state.not_null());
  if (hash_upd.old_hash != account.total_state->get_hash().bits()) {
    return reject_query(PSTRING() << "transaction " << lt << " of account " << addr.to_hex()
                                  << " claims that the original account state hash must be "
                                  << hash_upd.old_hash.to_hex() << " but the actual value is "
                                  << account.total_state->get_hash().to_hex());
  }
  // some type-specific checks
  int trans_type = block::transaction::Transaction::tr_none;
  switch (tag) {
    case block::gen::TransactionDescr::trans_ord: {
      trans_type = block::transaction::Transaction::tr_ord;
      if (in_msg_root.is_null()) {
        return reject_query(PSTRING() << "ordinary transaction " << lt << " of account " << addr.to_hex()
                                      << " has no inbound message");
      }
      need_credit_phase = !external;
      break;
    }
    case block::gen::TransactionDescr::trans_storage: {
      trans_type = block::transaction::Transaction::tr_storage;
      if (in_msg_root.not_null()) {
        return reject_query(PSTRING() << "storage transaction " << lt << " of account " << addr.to_hex()
                                      << " has an inbound message");
      }
      if (trans.outmsg_cnt) {
        return reject_query(PSTRING() << "storage transaction " << lt << " of account " << addr.to_hex()
                                      << " has at least one outbound message");
      }
      // FIXME
      return reject_query(PSTRING() << "unable to verify storage transaction " << lt << " of account "
                                    << addr.to_hex());
      break;
    }
    case block::gen::TransactionDescr::trans_tick_tock: {
      bool is_tock = (td_cs.prefetch_ulong(4) & 1);
      trans_type = is_tock ? block::transaction::Transaction::tr_tock : block::transaction::Transaction::tr_tick;
      if (in_msg_root.not_null()) {
        return reject_query(PSTRING() << (is_tock ? "tock" : "tick") << " transaction " << lt << " of account "
                                      << addr.to_hex() << " has an inbound message");
      }
      break;
    }
    case block::gen::TransactionDescr::trans_merge_prepare: {
      trans_type = block::transaction::Transaction::tr_merge_prepare;
      if (in_msg_root.not_null()) {
        return reject_query(PSTRING() << "merge prepare transaction " << lt << " of account " << addr.to_hex()
                                      << " has an inbound message");
      }
      if (trans.outmsg_cnt != 1) {
        return reject_query(PSTRING() << "merge prepare transaction " << lt << " of account " << addr.to_hex()
                                      << " must have exactly one outbound message");
      }
      // FIXME
      return reject_query(PSTRING() << "unable to verify merge prepare transaction " << lt << " of account "
                                    << addr.to_hex());
      break;
    }
    case block::gen::TransactionDescr::trans_merge_install: {
      trans_type = block::transaction::Transaction::tr_merge_install;
      if (in_msg_root.is_null()) {
        return reject_query(PSTRING() << "merge install transaction " << lt << " of account " << addr.to_hex()
                                      << " has no inbound message");
      }
      need_credit_phase = true;
      // FIXME
      return reject_query(PSTRING() << "unable to verify merge install transaction " << lt << " of account "
                                    << addr.to_hex());
      break;
    }
    case block::gen::TransactionDescr::trans_split_prepare: {
      trans_type = block::transaction::Transaction::tr_split_prepare;
      if (in_msg_root.not_null()) {
        return reject_query(PSTRING() << "split prepare transaction " << lt << " of account " << addr.to_hex()
                                      << " has an inbound message");
      }
      if (trans.outmsg_cnt > 1) {
        return reject_query(PSTRING() << "split prepare transaction " << lt << " of account " << addr.to_hex()
                                      << " must have exactly one outbound message");
      }
      // FIXME
      return reject_query(PSTRING() << "unable to verify split prepare transaction " << lt << " of account "
                                    << addr.to_hex());
      break;
    }
    case block::gen::TransactionDescr::trans_split_install: {
      trans_type = block::transaction::Transaction::tr_split_install;
      if (in_msg_root.is_null()) {
        return reject_query(PSTRING() << "split install transaction " << lt << " of account " << addr.to_hex()
                                      << " has no inbound message");
      }
      // FIXME
      return reject_query(PSTRING() << "unable to verify split install transaction " << lt << " of account "
                                    << addr.to_hex());
      break;
    }
  }
  // ....
  // check transaction computation by re-doing it
  // similar to Collator::create_ordinary_transaction() and Collator::create_ticktock_transaction()
  // ....
  std::unique_ptr<block::transaction::Transaction> trs =
      std::make_unique<block::transaction::Transaction>(account, trans_type, lt, now_, in_msg_root);
  if (in_msg_root.not_null()) {
    if (!trs->unpack_input_msg(ihr_delivered, &action_phase_cfg_)) {
      // inbound external message was not accepted
      return reject_query(PSTRING() << "could not unpack inbound " << (external ? "external" : "internal")
                                    << " message processed by ordinary transaction " << lt << " of account "
                                    << addr.to_hex());
    }
  }
  if (trs->bounce_enabled) {
    if (!trs->prepare_storage_phase(storage_phase_cfg_, true)) {
      return reject_query(PSTRING() << "cannot re-create storage phase of transaction " << lt << " for smart contract "
                                    << addr.to_hex());
    }
    if (need_credit_phase && !trs->prepare_credit_phase()) {
      return reject_query(PSTRING() << "cannot create re-credit phase of transaction " << lt << " for smart contract "
                                    << addr.to_hex());
    }
  } else {
    if (need_credit_phase && !trs->prepare_credit_phase()) {
      return reject_query(PSTRING() << "cannot re-create credit phase of transaction " << lt << " for smart contract "
                                    << addr.to_hex());
    }
    if (!trs->prepare_storage_phase(storage_phase_cfg_, true, need_credit_phase)) {
      return reject_query(PSTRING() << "cannot re-create storage phase of transaction " << lt << " for smart contract "
                                    << addr.to_hex());
    }
  }
  if (!trs->prepare_compute_phase(compute_phase_cfg_)) {
    return reject_query(PSTRING() << "cannot re-create compute phase of transaction " << lt << " for smart contract "
                                  << addr.to_hex());
  }
  if (!trs->compute_phase->accepted) {
    if (external) {
      return reject_query(PSTRING() << "inbound external message claimed to be processed by ordinary transaction " << lt
                                    << " of account " << addr.to_hex()
                                    << " was in fact rejected (such transaction cannot appear in valid blocks)");
    } else if (trs->compute_phase->skip_reason == block::ComputePhase::sk_none) {
      return reject_query(PSTRING() << "inbound internal message processed by ordinary transaction " << lt
                                    << " of account " << addr.to_hex() << " was not processed without any reason");
    }
  }
  if (trs->compute_phase->success && !trs->prepare_action_phase(action_phase_cfg_)) {
    return reject_query(PSTRING() << "cannot re-create action phase of transaction " << lt << " for smart contract "
                                  << addr.to_hex());
  }
  if (trs->bounce_enabled &&
      (!trs->compute_phase->success || trs->action_phase->state_exceeds_limits || trs->action_phase->bounce) &&
      !trs->prepare_bounce_phase(action_phase_cfg_)) {
    return reject_query(PSTRING() << "cannot re-create bounce phase of  transaction " << lt << " for smart contract "
                                  << addr.to_hex());
  }
  if (!trs->serialize()) {
    return reject_query(PSTRING() << "cannot re-create the serialization of  transaction " << lt
                                  << " for smart contract " << addr.to_hex());
  }
  if (!trs->update_limits(*block_limit_status_, /* with_gas = */ false, /* with_size = */ false)) {
    return fatal_error(PSTRING() << "cannot update block limit status to include transaction " << lt << " of account "
                                 << addr.to_hex());
  }

  // Collator should stop if total gas usage exceeds limits, including transactions on special accounts, but without
  // ticktocks and mint/recover.
  // Here Validator checks a weaker condition
  if (!is_special_tx && !trs->gas_limit_overridden && trans_type == block::transaction::Transaction::tr_ord) {
    (account.is_special ? total_special_gas_used_ : total_gas_used_) += trs->gas_used();
  }
  if (total_gas_used_ > block_limits_->gas.hard() + compute_phase_cfg_.gas_limit) {
    return reject_query(PSTRING() << "gas block limits are exceeded: total_gas_used > gas_limit_hard + trx_gas_limit ("
                                  << "total_gas_used=" << total_gas_used_
                                  << ", gas_limit_hard=" << block_limits_->gas.hard()
                                  << ", trx_gas_limit=" << compute_phase_cfg_.gas_limit << ")");
  }
  if (total_special_gas_used_ > block_limits_->gas.hard() + compute_phase_cfg_.special_gas_limit) {
    return reject_query(
        PSTRING() << "gas block limits are exceeded: total_special_gas_used > gas_limit_hard + special_gas_limit ("
                  << "total_special_gas_used=" << total_special_gas_used_
                  << ", gas_limit_hard=" << block_limits_->gas.hard()
                  << ", special_gas_limit=" << compute_phase_cfg_.special_gas_limit << ")");
  }

  auto trans_root2 = trs->commit(account);
  if (trans_root2.is_null()) {
    return reject_query(PSTRING() << "the re-created transaction " << lt << " for smart contract " << addr.to_hex()
                                  << " could not be committed");
  }
  // now compare the re-created transaction with the one we have
  if (trans_root2->get_hash() != trans_root->get_hash()) {
    if (verbosity >= 3 * 0) {
      std::cerr << "original transaction " << lt << " of " << addr.to_hex() << ": ";
      block::gen::t_Transaction.print_ref(std::cerr, trans_root);
      std::cerr << "re-created transaction " << lt << " of " << addr.to_hex() << ": ";
      block::gen::t_Transaction.print_ref(std::cerr, trans_root2);
    }
    return reject_query(PSTRING() << "the transaction " << lt << " of " << addr.to_hex() << " has hash "
                                  << trans_root->get_hash().to_hex()
                                  << " different from that of the recreated transaction "
                                  << trans_root2->get_hash().to_hex());
  }
  block::gen::Transaction::Record trans2;
  block::gen::HASH_UPDATE::Record hash_upd2;
  if (!(tlb::unpack_cell(trans_root2, trans2) &&
        tlb::type_unpack_cell(std::move(trans2.state_update), block::gen::t_HASH_UPDATE_Account, hash_upd2))) {
    return fatal_error(PSTRING() << "cannot unpack the re-created transaction " << lt << " of " << addr.to_hex());
  }
  if (hash_upd2.old_hash != hash_upd.old_hash) {
    return fatal_error(PSTRING() << "the re-created transaction " << lt << " of " << addr.to_hex()
                                 << " is invalid: it starts from account state with different hash");
  }
  if (hash_upd2.new_hash != account.total_state->get_hash().bits()) {
    return fatal_error(
        PSTRING() << "the re-created transaction " << lt << " of " << addr.to_hex()
                  << " is invalid: its claimed new account hash differs from the actual new account state");
  }
  if (hash_upd.new_hash != account.total_state->get_hash().bits()) {
    return reject_query(PSTRING() << "transaction " << lt << " of " << addr.to_hex()
                                  << " is invalid: it claims that the new account state hash is "
                                  << hash_upd.new_hash.to_hex() << " but the re-computed value is "
                                  << hash_upd2.new_hash.to_hex());
  }
  if (!trans.r1.out_msgs->contents_equal(*trans2.r1.out_msgs)) {
    return reject_query(
        PSTRING()
        << "transaction " << lt << " of " << addr.to_hex()
        << " is invalid: it has produced a set of outbound messages different from that listed in the transaction");
  }
  total_burned_ += trs->blackhole_burned;
  // check new balance and value flow
  auto new_balance = account.get_balance();
  block::CurrencyCollection total_fees;
  if (!total_fees.validate_unpack(trans.total_fees)) {
    return reject_query(PSTRING() << "transaction " << lt << " of " << addr.to_hex()
                                  << " has an invalid total_fees value");
  }
  if (old_balance + money_imported != new_balance + money_exported + total_fees + trs->blackhole_burned) {
    return reject_query(
        PSTRING() << "transaction " << lt << " of " << addr.to_hex()
                  << " violates the currency flow condition: old balance=" << old_balance.to_str()
                  << " + imported=" << money_imported.to_str() << " does not equal new balance=" << new_balance.to_str()
                  << " + exported=" << money_exported.to_str() << " + total_fees=" << total_fees.to_str()
                  << (trs->blackhole_burned.is_zero() ? ""
                                                      : PSTRING() << " burned=" << trs->blackhole_burned.to_str()));
  }
  return true;
}

}  // namespace solution
