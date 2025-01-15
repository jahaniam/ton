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
 * Checks the validity of the inbound messages listed in the InMsgDescr dictionary.
 *
 * @returns True if the inbound messages dictionary is valid, false otherwise.
 */
bool ContestValidateQuery::check_in_msg_descr() {
  LOG(INFO) << "checking inbound messages listed in InMsgDescr";
  try {
    CHECK(in_msg_dict_);
    if (!in_msg_dict_->validate_check_extra(
            [this](Ref<vm::CellSlice> value, Ref<vm::CellSlice> extra, td::ConstBitPtr key, int key_len) {
              CHECK(key_len == 256);
              return check_in_msg(key, std::move(value)) ||
                     reject_query("invalid InMsg with key (message hash) "s + key.to_hex(256) + " in the new block "s +
                                  id_.to_str());
            })) {
      return reject_query("invalid InMsgDescr dictionary in the new block "s + id_.to_str());
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid InMsgDescr dictionary: "s + err.get_msg());
  }
  return true;
}

/**
 * Checks the validity of an outbound message listed in OutMsgDescr.
 *
 * @param key The 256-bit key of the outbound message.
 * @param in_msg The outbound message to be checked serialized using OutMsg TLB-scheme.
 *
 * @returns True if the outbound message is valid, false otherwise.
 */
bool ContestValidateQuery::check_out_msg(td::ConstBitPtr key, Ref<vm::CellSlice> out_msg) {
  LOG(DEBUG) << "checking OutMsg with key " << key.to_hex(256);
  CHECK(out_msg.not_null());
  int tag = block::gen::t_OutMsg.get_tag(*out_msg);
  CHECK(tag >= 0);  // NB: the block has been already checked to be valid TL-B in try_validate()
  ton::StdSmcAddress src_addr;
  ton::WorkchainId src_wc;
  Ref<vm::CellSlice> src, dest;
  Ref<vm::Cell> transaction;
  Ref<vm::Cell> msg, msg_env, tr_msg_env, reimport;
  td::Bits256 msg_env_hash;
  // msg_envelope#4 cur_addr:IntermediateAddress next_addr:IntermediateAddress fwd_fee_remaining:Grams msg:^(Message Any) = MsgEnvelope;
  block::tlb::MsgEnvelope::Record_std env;
  // int_msg_info$0 ihr_disabled:Bool bounce:Bool bounced:Bool
  //   src:MsgAddressInt dest:MsgAddressInt
  //   value:CurrencyCollection ihr_fee:Grams fwd_fee:Grams
  //   created_lt:uint64 created_at:uint32 = CommonMsgInfo;
  block::gen::CommonMsgInfo::Record_int_msg_info info;
  ton::AccountIdPrefixFull src_prefix, dest_prefix, cur_prefix, next_prefix;
  td::RefInt256 fwd_fee, orig_fwd_fee;
  ton::LogicalTime import_lt = ~0ULL;
  unsigned long long created_lt = 0;
  int mode = 0, in_tag = -2;
  bool is_short = false;
  // initial checks and unpack
  switch (tag) {
    case block::gen::OutMsg::msg_export_ext: {
      // msg_export_ext$000 msg:^(Message Any) transaction:^Transaction = OutMsg;
      // exporting an outbound external message
      block::gen::CommonMsgInfo::Record_ext_out_msg_info info_ext;
      vm::CellSlice cs{*out_msg};
      CHECK(block::gen::t_OutMsg.unpack_msg_export_ext(cs, msg, transaction));
      if (msg->get_hash().as_bitslice() != key) {
        return reject_query("OutMsg with key "s + key.to_hex(256) + " refers to a message with different hash " +
                            msg->get_hash().to_hex());
      }
      if (!tlb::unpack_cell_inexact(msg, info_ext)) {
        return reject_query("OutMsg with key "s + key.to_hex(256) +
                            " is a msg_export_ext$000, but it does not refer to an outbound external message");
      }
      src_prefix = block::tlb::t_MsgAddressInt.get_prefix(info_ext.src);
      if (!src_prefix.is_valid()) {
        return reject_query("source of outbound external message with hash "s + key.to_hex(256) +
                            " is an invalid blockchain address");
      }
      if (!ton::shard_contains(shard_, src_prefix)) {
        return reject_query("outbound external message with hash "s + key.to_hex(256) + " has source address " +
                            src_prefix.to_str() + "... not in this shard");
      }
      src = std::move(info_ext.src);
      if (!block::tlb::t_MsgAddressInt.extract_std_address(src, src_wc, src_addr)) {
        return reject_query("cannot unpack source address of outbound external message with hash "s + key.to_hex(256));
      }
      break;
    }
    case block::gen::OutMsg::msg_export_imm: {
      block::gen::OutMsg::Record_msg_export_imm out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env));
      transaction = std::move(out.transaction);
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      reimport = std::move(out.reimport);
      in_tag = block::gen::InMsg::msg_import_imm;
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_new: {
      block::gen::OutMsg::Record_msg_export_new out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env) &&
            block::tlb::t_MsgEnvelope.get_emitted_lt(vm::load_cell_slice(out.out_msg), created_lt));
      transaction = std::move(out.transaction);
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      mode = 2;  // added to OutMsgQueue
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_tr: {
      block::gen::OutMsg::Record_msg_export_tr out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env));
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      reimport = std::move(out.imported);
      in_tag = block::gen::InMsg::msg_import_tr;
      mode = 2;  // added to OutMsgQueue
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_deq: {
      block::gen::OutMsg::Record_msg_export_deq out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env));
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      import_lt = out.import_block_lt;
      mode = 1;  // removed from OutMsgQueue
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_deq_short: {
      block::gen::OutMsg::Record_msg_export_deq_short out;
      CHECK(tlb::csr_unpack(out_msg, out));
      msg_env_hash = out.msg_env_hash;
      next_prefix.workchain = out.next_workchain;
      next_prefix.account_id_prefix = out.next_addr_pfx;
      import_lt = out.import_block_lt;
      is_short = true;
      mode = 1;  // removed from OutMsgQueue
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_tr_req: {
      block::gen::OutMsg::Record_msg_export_tr_req out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env));
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      reimport = std::move(out.imported);
      in_tag = block::gen::InMsg::msg_import_tr;
      mode = 3;  // removed from OutMsgQueue, and then added
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_deq_imm: {
      block::gen::OutMsg::Record_msg_export_deq_imm out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env));
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      reimport = std::move(out.reimport);
      in_tag = block::gen::InMsg::msg_import_fin;
      mode = 1;  // removed from OutMsgQueue (and processed)
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_new_defer: {
      block::gen::OutMsg::Record_msg_export_new_defer out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env) &&
            block::tlb::t_MsgEnvelope.get_emitted_lt(vm::load_cell_slice(out.out_msg), created_lt));
      transaction = std::move(out.transaction);
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_deferred_tr: {
      block::gen::OutMsg::Record_msg_export_deferred_tr out;
      CHECK(tlb::csr_unpack(out_msg, out) && tlb::unpack_cell(out.out_msg, env));
      msg_env = std::move(out.out_msg);
      msg = env.msg;
      reimport = std::move(out.imported);
      in_tag = block::gen::InMsg::msg_import_deferred_tr;
      mode = 2;  // added to OutMsgQueue
      if (!env.emitted_lt) {
        return reject_query(PSTRING() << "msg_export_deferred_tr for OutMsg with key " << key.to_hex(256)
                                      << " does not have emitted_lt in MsgEnvelope");
      }
      if (env.emitted_lt.value() < start_lt_ || env.emitted_lt.value() > end_lt_) {
        return reject_query(PSTRING() << "emitted_lt for msg_export_deferred_tr with key " << key.to_hex(256)
                                      << " is not between start and end lt of the block");
      }
      // ...
      break;
    }
    default:
      return reject_query(PSTRING() << "OutMsg with key (message hash) " << key.to_hex(256) << " has an unknown tag "
                                    << tag);
  }
  if (msg_env.not_null()) {
    msg_env_hash = msg_env->get_hash().bits();
  }

  // common checks for all (non-external) outbound messages
  if (!is_short) {
    CHECK(msg.not_null());
    if (msg->get_hash().as_bitslice() != key) {
      return reject_query("OutMsg with key "s + key.to_hex(256) + " refers to a message with different hash " +
                          msg->get_hash().to_hex());
    }
  }

  if (is_short) {
    // nothing to check here for msg_export_deq_short ?
  } else if (tag != block::gen::OutMsg::msg_export_ext) {
    // unpack int_msg_info$0 ... = CommonMsgInfo, especially message addresses
    if (!tlb::unpack_cell_inexact(msg, info)) {
      return reject_query("OutMsg with key "s + key.to_hex(256) +
                          " is not a msg_export_ext$000, but it does not refer to an internal message");
    }
    // extract source, current, next hop and destination address prefixes
    if (!block::tlb::t_MsgAddressInt.get_prefix_to(info.src, src_prefix)) {
      return reject_query("source of outbound internal message with hash "s + key.to_hex(256) +
                          " is an invalid blockchain address");
    }
    if (!block::tlb::t_MsgAddressInt.get_prefix_to(info.dest, dest_prefix)) {
      return reject_query("destination of outbound internal message with hash "s + key.to_hex(256) +
                          " is an invalid blockchain address");
    }
    if (tag == block::gen::OutMsg::msg_export_new_defer) {
      if (env.cur_addr != 0 || env.next_addr != 0) {
        return reject_query("cur_addr and next_addr of the message in DispatchQueue must be zero");
      }
    } else {
      cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.cur_addr);
      next_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.next_addr);
      if (!(cur_prefix.is_valid() && next_prefix.is_valid())) {
        return reject_query("cannot compute current and next hop addresses of outbound internal message with hash "s +
                            key.to_hex(256));
      }
      // check that next hop is nearer to the destination than the current address
      if (count_matching_bits(dest_prefix, next_prefix) < count_matching_bits(dest_prefix, cur_prefix)) {
        return reject_query("next hop address "s + next_prefix.to_str() +
                            "... of outbound internal message with hash " + key.to_hex(256) +
                            " is further from its destination " + dest_prefix.to_str() +
                            "... than its current address " + cur_prefix.to_str() + "...");
      }
      // current address must belong to this shard (otherwise we should never had exported this message)
      if (!ton::shard_contains(shard_, cur_prefix)) {
        return reject_query("current address "s + cur_prefix.to_str() + "... of outbound internal message with hash " +
                            key.to_hex(256) + " does not belong to the current block's shard " + shard_.to_str());
      }
      // next hop may coincide with current address only if destination is already reached
      if (next_prefix == cur_prefix && cur_prefix != dest_prefix) {
        return reject_query(
            "next hop address "s + next_prefix.to_str() + "... of outbound internal message with hash " +
            key.to_hex(256) +
            " coincides with its current address, but this message has not reached its final destination " +
            dest_prefix.to_str() + "... yet");
      }
    }
    // if a message is created by a transaction, it must have source inside the current shard
    if (transaction.not_null() && !ton::shard_contains(shard_, src_prefix)) {
      return reject_query("outbound internal message with hash "s + key.to_hex(256) + " has source address " +
                          src_prefix.to_str() +
                          "... not in this shard, but it has been created here by a Transaction nonetheless");
    }
    src = std::move(info.src);
    dest = std::move(info.dest);
    // unpack complete source address if it is inside this shard
    if (!block::tlb::t_MsgAddressInt.extract_std_address(src, src_wc, src_addr)) {
      return reject_query("cannot unpack source address of outbound internal message with hash "s + key.to_hex(256) +
                          " created in this shard");
    }
    // unpack original forwarding fee
    orig_fwd_fee = block::tlb::t_Grams.as_integer(info.fwd_fee);
    CHECK(orig_fwd_fee.not_null());
    if (env.fwd_fee_remaining > orig_fwd_fee) {
      return reject_query("outbound internal message with hash "s + key.to_hex(256) + " has remaining forwarding fee " +
                          td::dec_string(env.fwd_fee_remaining) + " larger than the original (total) forwarding fee " +
                          td::dec_string(orig_fwd_fee));
    }
  }

  if (transaction.not_null()) {
    // check that the transaction reference is valid, and that it points to a Transaction which indeed creates this outbound internal message
    if (!is_valid_transaction_ref(transaction)) {
      return reject_query(
          "OutMsg corresponding to outbound message with key "s + key.to_hex(256) +
          " contains an invalid Transaction reference (transaction not in the block's transaction list)");
    }
    if (!block::is_transaction_out_msg(transaction, msg)) {
      return reject_query("OutMsg corresponding to outbound message with key "s + key.to_hex(256) +
                          " refers to transaction that does not create this outbound message");
    }
    ton::StdSmcAddress trans_addr;
    ton::LogicalTime trans_lt;
    CHECK(block::get_transaction_id(transaction, trans_addr, trans_lt));
    if (src_addr != trans_addr) {
      block::gen::t_OutMsg.print(std::cerr, *out_msg);
      return reject_query(PSTRING() << "OutMsg corresponding to outbound message with hash " << key.to_hex(256)
                                    << " and source address " << src_addr.to_hex()
                                    << " claims that the message was created by transaction " << trans_lt
                                    << " of another account " << trans_addr.to_hex());
    }
    // LOG(DEBUG) << "OutMsg " << key.to_hex(256) + " is indeed a valid outbound message of transaction " << trans_lt
    //           << " of " << trans_addr.to_hex();
  }

  if (tag == block::gen::OutMsg::msg_export_ext) {
    return true;  // nothing to check more for external messages
  }

  // check the OutMsgQueue update effected by this OutMsg
  td::BitArray<32 + 64 + 256> q_key;
  q_key.bits().store_int(next_prefix.workchain, 32);
  (q_key.bits() + 32).store_int(next_prefix.account_id_prefix, 64);
  (q_key.bits() + 96).copy_from(key, 256);
  auto q_entry = ns_.out_msg_queue_->lookup(q_key);
  auto old_q_entry = ps_.out_msg_queue_->lookup(q_key);

  if (tag == block::gen::OutMsg::msg_export_new_defer) {
    // check the DispatchQueue update
    if (old_q_entry.not_null() || q_entry.not_null()) {
      return reject_query("OutMsg with key (message hash) "s + key.to_hex(256) +
                          " shouldn't exist in the old and the new message queues");
    }
    auto it = new_dispatch_queue_messages_.find({src_addr, created_lt});
    if (it == new_dispatch_queue_messages_.end()) {
      return reject_query(PSTRING() << "new deferred OutMsg with src_addr=" << src_addr.to_hex()
                                    << ", lt=" << created_lt << " was not added to the dispatch queue");
    }
    Ref<vm::Cell> expected_msg_env = it->second;
    if (expected_msg_env->get_hash() != msg_env->get_hash()) {
      return reject_query(PSTRING() << "new deferred OutMsg with src_addr=" << src_addr.to_hex() << ", lt="
                                    << created_lt << " msg envelope hasg mismatch: " << msg_env->get_hash().to_hex()
                                    << " in OutMsg, " << expected_msg_env->get_hash().to_hex() << " in DispatchQueue");
    }
    new_dispatch_queue_messages_.erase(it);
  } else {
    if (old_q_entry.not_null() && q_entry.not_null()) {
      return reject_query("OutMsg with key (message hash) "s + key.to_hex(256) +
                          " should have removed or added OutMsgQueue entry with key " + q_key.to_hex() +
                          ", but it is present both in the old and in the new output queues");
    }
    if (old_q_entry.is_null() && q_entry.is_null() && mode) {
      return reject_query("OutMsg with key (message hash) "s + key.to_hex(256) +
                          " should have removed or added OutMsgQueue entry with key " + q_key.to_hex() +
                          ", but it is absent both from the old and from the new output queues");
    }
    if (!mode && (old_q_entry.not_null() || q_entry.not_null())) {
      return reject_query("OutMsg with key (message hash) "s + key.to_hex(256) +
                          " is a msg_export_imm$010, so the OutMsgQueue entry with key " + q_key.to_hex() +
                          " should never be created, but it is present in either the old or the new output queue");
    }
    // NB: if mode!=0, the OutMsgQueue entry has been changed, so we have already checked some conditions in precheck_one_message_queue_update()
    if (mode & 2) {
      if (q_entry.is_null()) {
        return reject_query("OutMsg with key "s + key.to_hex(256) +
                            " was expected to create OutMsgQueue entry with key " + q_key.to_hex() + " but it did not");
      }
      if (msg_env_hash != q_entry->prefetch_ref()->get_hash().bits()) {
        return reject_query("OutMsg with key "s + key.to_hex(256) + " has created OutMsgQueue entry with key " +
                            q_key.to_hex() + " containing a different MsgEnvelope");
      }
      // ...
    } else if (mode & 1) {
      if (old_q_entry.is_null()) {
        return reject_query("OutMsg with key "s + key.to_hex(256) +
                            " was expected to remove OutMsgQueue entry with key " + q_key.to_hex() +
                            " but it did not exist in the old queue");
      }
      if (msg_env_hash != old_q_entry->prefetch_ref()->get_hash().bits()) {
        return reject_query("OutMsg with key "s + key.to_hex(256) + " has dequeued OutMsgQueue entry with key " +
                            q_key.to_hex() + " containing a different MsgEnvelope");
      }
      // ...
    }
  }

  // check reimport:^InMsg
  if (reimport.not_null()) {
    // transit message: msg_export_tr + msg_import_tr
    // or message re-imported from this very shard
    // either msg_export_imm + msg_import_imm
    // or msg_export_deq_imm + msg_import_fin (rarely)
    // or msg_export_tr_req + msg_import_tr (rarely)
    // (the last two cases possible only after merge)
    //
    // check that reimport is a valid InMsg registered in InMsgDescr
    auto in = in_msg_dict_->lookup(key, 256);
    if (in.is_null()) {
      return reject_query("OutMsg with key "s + key.to_hex(256) +
                          " refers to a (re)import InMsg, but there is no InMsg with such a key");
    }
    if (!in->contents_equal(vm::load_cell_slice(reimport))) {
      return reject_query(
          "OutMsg with key "s + key.to_hex(256) +
          " refers to a (re)import InMsg, but the actual InMsg with this key is different from the one referred to");
    }
    // NB: in check_in_msg(), we have already checked that all InMsg have correct keys (equal to the hash of the imported message), so the imported message is equal to the exported message (they have the same hash)
    // have only to check the envelope
    int i_tag = block::gen::t_InMsg.get_tag(*in);
    if (i_tag < 0 || i_tag != in_tag) {
      return reject_query("OutMsg with key "s + key.to_hex(256) +
                          " refers to a (re)import InMsg, which is not one of msg_import_imm, msg_import_fin, "
                          "msg_import_tr or msg_import_deferred_tr as expected");
    }
  }

  // ...
  switch (tag) {
    case block::gen::OutMsg::msg_export_imm: {
      block::gen::InMsg::Record_msg_import_imm in;
      block::tlb::MsgEnvelope::Record_std in_env;
      if (!(tlb::unpack_cell(reimport, in) && tlb::unpack_cell(in.in_msg, in_env))) {
        return reject_query(
            "cannot unpack msg_import_imm InMsg record corresponding to msg_export_imm OutMsg record with key "s +
            key.to_hex(256));
      }
      if (in.in_msg->get_hash() != msg_env->get_hash()) {
        return reject_query("msg_import_imm InMsg record corresponding to msg_export_imm OutMsg record with key "s +
                            key.to_hex(256) + " re-imported a different MsgEnvelope");
      }
      if (!shard_contains(shard_, dest_prefix)) {
        return reject_query("msg_export_imm OutMsg record with key "s + key.to_hex(256) +
                            " refers to a message with destination " + dest_prefix.to_str() + " outside this shard");
      }
      if (cur_prefix != dest_prefix || next_prefix != dest_prefix) {
        return reject_query("msg_export_imm OutMsg record with key "s + key.to_hex(256) +
                            " refers to a message that has not been routed to its final destination");
      }
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_new: {
      // perform hypercube routing for this new message
      auto route_info = block::perform_hypercube_routing(src_prefix, dest_prefix, shard_);
      if ((unsigned)route_info.first > 96 || (unsigned)route_info.second > 96) {
        return reject_query("cannot perform (check) hypercube routing for new outbound message with hash "s +
                            key.to_hex(256));
      }
      auto new_cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, route_info.first);
      auto new_next_prefix = block::interpolate_addr(src_prefix, dest_prefix, route_info.second);
      if (cur_prefix != new_cur_prefix || next_prefix != new_next_prefix) {
        return reject_query("OutMsg for new message with hash "s + key.to_hex(256) +
                            " tells us that it has been routed to current address " + cur_prefix.to_str() +
                            "... and hext hop address " + next_prefix.to_str() +
                            " while the correct values dictated by hypercube routing are " + new_cur_prefix.to_str() +
                            "... and " + new_next_prefix.to_str() + "...");
      }
      CHECK(shard_contains(shard_, src_prefix));
      if (shard_contains(shard_, dest_prefix)) {
        // LOG(DEBUG) << "(THIS) src=" << src_prefix.to_str() << " cur=" << cur_prefix.to_str() << " next=" << next_prefix.to_str() << " dest=" << dest_prefix.to_str() << " route_info=(" << route_info.first << "," << route_info.second << ")";
        CHECK(cur_prefix == dest_prefix);
        CHECK(next_prefix == dest_prefix);
        update_min_enqueued_lt_hash(created_lt, msg->get_hash().bits());
      } else {
        // sanity check of the implementation of hypercube routing
        // LOG(DEBUG) << "(THAT) src=" << src_prefix.to_str() << " cur=" << cur_prefix.to_str() << " next=" << next_prefix.to_str() << " dest=" << dest_prefix.to_str();
        CHECK(shard_contains(shard_, cur_prefix));
        CHECK(!shard_contains(shard_, next_prefix));
      }
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_new_defer: {
      break;
    }
    case block::gen::OutMsg::msg_export_tr: {
      block::gen::InMsg::Record_msg_import_tr in;
      block::tlb::MsgEnvelope::Record_std in_env;
      if (!(tlb::unpack_cell(reimport, in) && tlb::unpack_cell(in.in_msg, in_env))) {
        return reject_query(
            "cannot unpack msg_import_tr InMsg record corresponding to msg_export_tr OutMsg record with key "s +
            key.to_hex(256));
      }
      CHECK(in_env.msg->get_hash() == msg->get_hash());
      auto in_cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, in_env.cur_addr);
      auto in_next_prefix = block::interpolate_addr(src_prefix, dest_prefix, in_env.next_addr);
      if (shard_contains(shard_, in_cur_prefix)) {
        return reject_query("msg_export_tr OutMsg record with key "s + key.to_hex(256) +
                            " corresponds to msg_import_tr InMsg record with current imported message address " +
                            in_cur_prefix.to_str() +
                            " inside the current shard (msg_export_tr_req should have been used instead)");
      }
      // we have already checked correctness of hypercube routing in InMsg::msg_import_tr case of check_in_msg()
      CHECK(shard_contains(shard_, in_next_prefix));
      CHECK(shard_contains(shard_, cur_prefix));
      CHECK(!shard_contains(shard_, next_prefix));
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_deferred_tr: {
      block::gen::InMsg::Record_msg_import_deferred_tr in;
      block::tlb::MsgEnvelope::Record_std in_env;
      if (!(tlb::unpack_cell(reimport, in) && tlb::unpack_cell(in.in_msg, in_env))) {
        return reject_query(
            "cannot unpack msg_import_deferred_tr InMsg record corresponding to msg_export_deferred_tr OutMsg record with key "s +
            key.to_hex(256));
      }
      CHECK(in_env.msg->get_hash() == msg->get_hash());
      auto in_cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, in_env.cur_addr);
      if (!shard_contains(shard_, in_cur_prefix)) {
        return reject_query(
            "msg_export_deferred_tr OutMsg record with key "s + key.to_hex(256) +
            " corresponds to msg_import_deferred_tr InMsg record with current imported message address " +
            in_cur_prefix.to_str() + " NOT inside the current shard");
      }
      break;
    }
    case block::gen::OutMsg::msg_export_deq:
    case block::gen::OutMsg::msg_export_deq_short: {
      // check that the message has been indeed processed by a neighbor
      CHECK(old_q_entry.not_null());
      block::EnqueuedMsgDescr enq_msg_descr;
      if (!enq_msg_descr.unpack(old_q_entry.write())) {  // unpack EnqueuedMsg
        return reject_query(
            "cannot unpack old OutMsgQueue entry corresponding to msg_export_deq OutMsg entry with key "s +
            key.to_hex(256));
      }
      bool delivered = false;
      ton::LogicalTime deliver_lt = 0;
      for (const auto& neighbor : neighbors_) {
        // could look up neighbor with shard containing enq_msg_descr.next_prefix more efficiently
        // (instead of checking all neighbors)
        if (!neighbor.is_disabled() && neighbor.processed_upto->already_processed(enq_msg_descr)) {
          delivered = true;
          deliver_lt = neighbor.end_lt();
          break;
        }
      }
      if (!delivered) {
        return reject_query("msg_export_deq OutMsg entry with key "s + key.to_hex(256) +
                            " attempts to dequeue a message with next hop " + next_prefix.to_str() +
                            " that has not been yet processed by the corresponding neighbor");
      }
      if (deliver_lt != import_lt) {
        LOG(INFO) << "msg_export_deq OutMsg entry with key " << key.to_hex(256)
                     << " claims the dequeued message with next hop "
                     << next_prefix.to_str() + " has been delivered in block with end_lt=" << import_lt
                     << " while the correct value is " << deliver_lt;
      }
      break;
    }
    case block::gen::OutMsg::msg_export_tr_req: {
      block::gen::InMsg::Record_msg_import_tr in;
      block::tlb::MsgEnvelope::Record_std in_env;
      if (!(tlb::unpack_cell(reimport, in) && tlb::unpack_cell(in.in_msg, in_env))) {
        return reject_query(
            "cannot unpack msg_import_tr InMsg record corresponding to msg_export_tr_req OutMsg record with key "s +
            key.to_hex(256));
      }
      CHECK(in_env.msg->get_hash() == msg->get_hash());
      auto in_cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, in_env.cur_addr);
      auto in_next_prefix = block::interpolate_addr(src_prefix, dest_prefix, in_env.next_addr);
      if (!shard_contains(shard_, in_cur_prefix)) {
        return reject_query("msg_export_tr_req OutMsg record with key "s + key.to_hex(256) +
                            " corresponds to msg_import_tr InMsg record with current imported message address " +
                            in_cur_prefix.to_str() +
                            " outside the current shard (msg_export_tr should have been used instead, because there "
                            "was no re-queueing)");
      }
      // we have already checked correctness of hypercube routing in InMsg::msg_import_tr case of check_in_msg()
      CHECK(shard_contains(shard_, in_next_prefix));
      CHECK(shard_contains(shard_, cur_prefix));
      CHECK(!shard_contains(shard_, next_prefix));
      // so we have just to check that the rewritten message (envelope) has been enqueued
      // (already checked above for q_entry since mode = 3)
      // and that the original message (envelope) has been dequeued
      q_key.bits().store_int(in_next_prefix.workchain, 32);
      (q_key.bits() + 32).store_int(in_next_prefix.account_id_prefix, 64);
      q_entry = ns_.out_msg_queue_->lookup(q_key);
      old_q_entry = ps_.out_msg_queue_->lookup(q_key);
      if (old_q_entry.is_null()) {
        return reject_query("msg_export_tr_req OutMsg record with key "s + key.to_hex(256) +
                            " was expected to dequeue message from OutMsgQueue with key "s + q_key.to_hex() +
                            " but such a message is absent from the old OutMsgQueue");
      }
      if (q_entry.not_null()) {
        return reject_query("msg_export_tr_req OutMsg record with key "s + key.to_hex(256) +
                            " was expected to dequeue message from OutMsgQueue with key "s + q_key.to_hex() +
                            " but such a message is still present in the new OutMsgQueue");
      }
      block::EnqueuedMsgDescr enq_msg_descr;
      if (!enq_msg_descr.unpack(old_q_entry.write())) {  // unpack EnqueuedMsg
        return reject_query(
            "cannot unpack old OutMsgQueue entry corresponding to msg_export_tr_req OutMsg entry with key "s +
            key.to_hex(256));
      }
      if (enq_msg_descr.msg_env_->get_hash() != in.in_msg->get_hash()) {
        return reject_query("msg_import_tr InMsg entry corresponding to msg_export_tr_req OutMsg entry with key "s +
                            key.to_hex(256) +
                            " has re-imported a different MsgEnvelope from that present in the old OutMsgQueue");
      }
      // ...
      break;
    }
    case block::gen::OutMsg::msg_export_deq_imm: {
      block::gen::InMsg::Record_msg_import_fin in;
      block::tlb::MsgEnvelope::Record_std in_env;
      if (!(tlb::unpack_cell(reimport, in) && tlb::unpack_cell(in.in_msg, in_env))) {
        return reject_query(
            "cannot unpack msg_import_fin InMsg record corresponding to msg_export_deq_imm OutMsg record with key "s +
            key.to_hex(256));
      }
      if (in.in_msg->get_hash() != msg_env->get_hash()) {
        return reject_query("msg_import_fin InMsg record corresponding to msg_export_deq_imm OutMsg record with key "s +
                            key.to_hex(256) +
                            " somehow imported a different MsgEnvelope from that dequeued by msg_export_deq_imm");
      }
      if (!shard_contains(shard_, cur_prefix)) {
        return reject_query("msg_export_deq_imm OutMsg record with key "s + key.to_hex(256) +
                            " dequeued a MsgEnvelope with current address " + cur_prefix.to_str() +
                            "... outside current shard");
      }
      // we have already checked more conditions in check_in_msg() case msg_import_fin
      CHECK(shard_contains(shard_, next_prefix));  // sanity check
      CHECK(shard_contains(shard_, dest_prefix));  // sanity check
      // ...
      break;
    }
    default:
      return fatal_error(PSTRING() << "unknown OutMsg tag " << tag);
  }

  if (tag == block::gen::OutMsg::msg_export_imm || tag == block::gen::OutMsg::msg_export_deq_imm ||
      tag == block::gen::OutMsg::msg_export_new || tag == block::gen::OutMsg::msg_export_deferred_tr) {
    if (src_wc != workchain()) {
      return true;
    }
    if (tag == block::gen::OutMsg::msg_export_imm && is_special_in_msg(vm::load_cell_slice(reimport))) {
      return true;
    }
    unsigned long long created_lt;
    auto cs = vm::load_cell_slice(env.msg);
    if (!block::tlb::t_Message.get_created_lt(cs, created_lt)) {
      return reject_query(PSTRING() << "cannot get created_lt for OutMsg with key " << key.to_hex(256)
                                    << ", tag=" << tag);
    }
    auto emitted_lt = env.emitted_lt ? env.emitted_lt.value() : created_lt;
    msg_emitted_lt_.emplace_back(src_addr, created_lt, emitted_lt);
  }

  return true;
}

/**
 * Checks the validity of the outbound messages listed in the OutMsgDescr dictionary.
 *
 * @returns True if the outbound messages dictionary is valid, false otherwise.
 */
bool ContestValidateQuery::check_out_msg_descr() {
  LOG(INFO) << "checking outbound messages listed in OutMsgDescr";
  try {
    CHECK(out_msg_dict_);
    if (!out_msg_dict_->validate_check_extra(
            [this](Ref<vm::CellSlice> value, Ref<vm::CellSlice> extra, td::ConstBitPtr key, int key_len) {
              CHECK(key_len == 256);
              return check_out_msg(key, std::move(value)) ||
                     reject_query("invalid OutMsg with key "s + key.to_hex(256) + " in the new block "s + id_.to_str());
            })) {
      return reject_query("invalid OutMsgDescr dictionary in the new block "s + id_.to_str());
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid OutMsgDescr dictionary: "s + err.get_msg());
  }
  return true;
}

/**
 * Checks if the processed up to information is valid and consistent.
 * Compare to Collator::update_processed_upto()
 *
 * @returns True if the processed up to information is valid and consistent, false otherwise.
 */
bool ContestValidateQuery::check_processed_upto() {
  LOG(INFO) << "checking ProcessedInfo";
  CHECK(ps_.processed_upto_);
  CHECK(ns_.processed_upto_);
  if (!ns_.processed_upto_->is_reduced()) {
    return reject_query("new ProcessedInfo is not reduced (some entries completely cover other entries)");
  }
  bool ok = false;
  auto upd = ns_.processed_upto_->is_simple_update_of(*ps_.processed_upto_, ok);
  if (!ok) {
    return reject_query("new ProcessedInfo is not obtained from old ProcessedInfo by adding at most one new entry");
  }
  processed_upto_updated_ = upd;
  if (upd) {
    if (upd->shard != shard_.shard) {
      return reject_query("newly-added ProcessedInfo entry refers to shard "s +
                          ShardIdFull{workchain(), upd->shard}.to_str() + " distinct from the current shard " +
                          shard_.to_str());
    }
    auto ref_mc_seqno = mc_seqno_;
    if (upd->mc_seqno != ref_mc_seqno) {
      return reject_query(PSTRING() << "newly-added ProcessedInfo entry refers to masterchain block " << upd->mc_seqno
                                    << " but the processed inbound message queue belongs to masterchain block "
                                    << ref_mc_seqno);
    }
    if (upd->last_inmsg_lt >= end_lt_) {
      return reject_query(PSTRING() << "newly-added ProcessedInfo entry claims that the last processed message has lt "
                                    << upd->last_inmsg_lt << " larger than this block's end lt " << end_lt_);
    }
    if (!upd->last_inmsg_lt) {
      return reject_query("newly-added ProcessedInfo entry claims that the last processed message has zero lt");
    }
    claimed_proc_lt_ = upd->last_inmsg_lt;
    claimed_proc_hash_ = upd->last_inmsg_hash;
  } else {
    claimed_proc_lt_ = 0;
    claimed_proc_hash_.set_zero();
  }
  LOG(INFO) << "ProcessedInfo claims to have processed all inbound messages up to (" << claimed_proc_lt_ << ","
            << claimed_proc_hash_.to_hex() << ")";
  if (claimed_proc_lt_ < proc_lt_ || (claimed_proc_lt_ == proc_lt_ && proc_lt_ && claimed_proc_hash_ < proc_hash_)) {
    return reject_query(PSTRING() << "the ProcessedInfo claims to have processed messages only upto ("
                                  << claimed_proc_lt_ << "," << claimed_proc_hash_.to_hex()
                                  << "), but there is a InMsg processing record for later message (" << proc_lt_ << ","
                                  << proc_hash_.to_hex());
  }
  if (min_enq_lt_ < claimed_proc_lt_ || (min_enq_lt_ == claimed_proc_lt_ && !(claimed_proc_hash_ < min_enq_hash_))) {
    return reject_query(PSTRING() << "the ProcessedInfo claims to have processed all messages upto ("
                                  << claimed_proc_lt_ << "," << claimed_proc_hash_.to_hex()
                                  << "), but there is a OutMsg enqueuing record for earlier message (" << min_enq_lt_
                                  << "," << min_enq_hash_.to_hex());
  }
  // ...
  return true;
}


}  // namespace solution
