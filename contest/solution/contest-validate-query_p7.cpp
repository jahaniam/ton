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
 * Pre-validates all account blocks.
 *
 * @returns True if the pre-checking is successful, otherwise false.
 */
bool ContestValidateQuery::precheck_account_transactions() {
  LOG(INFO) << "pre-checking all AccountBlocks, and all transactions of all accounts";
  try {
    CHECK(account_blocks_dict_);
    if (!account_blocks_dict_->validate_check_extra(
            [this](Ref<vm::CellSlice> value, Ref<vm::CellSlice> extra, td::ConstBitPtr key, int key_len) {
              CHECK(key_len == 256);
              return precheck_one_account_block(key, std::move(value)) ||
                     reject_query("invalid AccountBlock for account "s + key.to_hex(256) + " in the new block "s +
                                  id_.to_str());
            })) {
      return reject_query("invalid ShardAccountBlock dictionary in the new block "s + id_.to_str());
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid ShardAccountBlocks dictionary: "s + err.get_msg());
  }
  return true;
}

/**
 * Looks up a transaction in the account blocks dictionary for a given account address and logical time.
 *
 * @param addr The address of the account.
 * @param lt The logical time of the transaction.
 *
 * @returns A reference to the transaction if found, null otherwise.
 */
Ref<vm::Cell> ContestValidateQuery::lookup_transaction(const ton::StdSmcAddress& addr, ton::LogicalTime lt) const {
  CHECK(account_blocks_dict_);
  block::gen::AccountBlock::Record ab_rec;
  if (!tlb::csr_unpack_safe(account_blocks_dict_->lookup(addr), ab_rec)) {
    return {};
  }
  vm::AugmentedDictionary trans_dict{vm::DictNonEmpty(), std::move(ab_rec.transactions), 64,
                                     block::tlb::aug_AccountTransactions};
  return trans_dict.lookup_ref(td::BitArray<64>{(long long)lt});
}

/**
 * Checks that a Transaction cell refers to a transaction present in the ShardAccountBlocks.
 *
 * @param trans_ref The reference to the serialized transaction root.
 *
 * @returns True if the transaction reference is valid, False otherwise.
 */
bool ContestValidateQuery::is_valid_transaction_ref(Ref<vm::Cell> trans_ref) const {
  ton::StdSmcAddress addr;
  ton::LogicalTime lt;
  if (!block::get_transaction_id(trans_ref, addr, lt)) {
    LOG(DEBUG) << "cannot parse transaction header";
    return false;
  }
  auto trans = lookup_transaction(addr, lt);
  if (trans.is_null()) {
    LOG(DEBUG) << "transaction " << lt << " of " << addr.to_hex() << " not found";
    return false;
  }
  if (trans->get_hash() != trans_ref->get_hash()) {
    LOG(DEBUG) << "transaction " << lt << " of " << addr.to_hex() << " has a different hash";
    return false;
  }
  return true;
}

bool ContestValidateQuery::build_new_message_queue() {
  ns_.out_msg_queue_ =
      std::make_unique<vm::AugmentedDictionary>(ps_.out_msg_queue_->get_root(), 352, block::tlb::aug_OutMsgQueue);
  ns_.dispatch_queue_ =
      std::make_unique<vm::AugmentedDictionary>(ps_.dispatch_queue_->get_root(), 256, block::tlb::aug_DispatchQueue);
  ns_.out_msg_queue_size_ = ps_.out_msg_queue_size_.value();

  bool ok = in_msg_dict_->check_for_each_extra([&](Ref<vm::CellSlice> value, Ref<vm::CellSlice>, td::ConstBitPtr, int) {
    int tag = block::gen::t_InMsg.get_tag(*value);
    switch (tag) {
      case block::gen::InMsg::msg_import_ext: {
        break;
      }
      case block::gen::InMsg::msg_import_deferred_fin: {
        block::gen::InMsg::Record_msg_import_deferred_fin rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        CHECK(block::gen::csr_unpack(value, rec));
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.in_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_import_deferred_fin");
        }

        WorkchainId wc;
        StdSmcAddress addr;
        if (!block::tlb::t_MsgAddressInt.extract_std_address(msg.src, wc, addr)) {
          return fatal_error("failed to extract src address for msg_import_deferred_fin");
        }
        if (!block::remove_dispatch_queue_entry(*ns_.dispatch_queue_, addr, msg.created_lt)) {
          return fatal_error("failed to remove dispatch queue entry for msg_import_deferred_fin");
        }
        break;
      }
      case block::gen::InMsg::msg_import_deferred_tr: {
        block::gen::InMsg::Record_msg_import_deferred_tr rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        CHECK(block::gen::csr_unpack(value, rec));
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.in_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_import_deferred_tr");
        }

        WorkchainId wc;
        StdSmcAddress addr;
        if (!block::tlb::t_MsgAddressInt.extract_std_address(msg.src, wc, addr)) {
          return fatal_error("failed to extract src address for msg_import_deferred_tr");
        }
        if (!block::remove_dispatch_queue_entry(*ns_.dispatch_queue_, addr, msg.created_lt)) {
          return fatal_error("failed to remove dispatch queue entry for msg_import_deferred_tr");
        }
        break;
      }
      case block::gen::InMsg::msg_import_ihr: {
        break;
      }
      case block::gen::InMsg::msg_import_imm: {
        break;
      }
      case block::gen::InMsg::msg_import_fin: {
        break;
      }
      case block::gen::InMsg::msg_import_tr: {
        break;
      }
      case block::gen::InMsg::msg_discard_fin: {
        break;
      }
      case block::gen::InMsg::msg_discard_tr: {
        break;
      }
    }
    return true;
  });
  if (!ok) {
    return reject_query("failed to parse in msg dict");
  }
  ok = out_msg_dict_->check_for_each_extra([&](Ref<vm::CellSlice> value, Ref<vm::CellSlice>, td::ConstBitPtr key, int) {
    int tag = block::gen::t_OutMsg.get_tag(*value);
    switch (tag) {
      case block::gen::OutMsg::msg_export_ext: {
        break;
      }
      case block::gen::OutMsg::msg_export_new: {
        block::gen::OutMsg::Record_msg_export_new rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        CHECK(block::gen::csr_unpack(value, rec));
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.out_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_export_new");
        }
        LogicalTime enqueued_lt = msg.created_lt;

        auto src_prefix = block::tlb::MsgAddressInt::get_prefix(msg.src);
        auto dest_prefix = block::tlb::MsgAddressInt::get_prefix(msg.dest);
        auto next_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.next_addr);

        td::BitArray<32 + 64 + 256> queue_key;
        td::BitPtr ptr = queue_key.bits();
        ptr.store_int(next_prefix.workchain, 32);
        ptr.advance(32);
        ptr.store_uint(next_prefix.account_id_prefix, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        vm::CellBuilder cb;
        CHECK(cb.store_long_bool(enqueued_lt) && cb.store_ref_bool(rec.out_msg));
        if (!ns_.out_msg_queue_->set_builder(queue_key, cb, vm::Dictionary::SetMode::Add)) {
          return fatal_error("failed to store message to out msg queue for msg_export_new");
        }
        ++ns_.out_msg_queue_size_.value();
        break;
      }
      case block::gen::OutMsg::msg_export_imm: {
        break;
      }
      case block::gen::OutMsg::msg_export_tr: {
        block::gen::OutMsg::Record_msg_export_tr rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        CHECK(block::gen::csr_unpack(value, rec));
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.out_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_export_tr");
        }
        LogicalTime enqueued_lt = start_lt_;

        auto src_prefix = block::tlb::MsgAddressInt::get_prefix(msg.src);
        auto dest_prefix = block::tlb::MsgAddressInt::get_prefix(msg.dest);
        auto next_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.next_addr);

        td::BitArray<32 + 64 + 256> queue_key;
        td::BitPtr ptr = queue_key.bits();
        ptr.store_int(next_prefix.workchain, 32);
        ptr.advance(32);
        ptr.store_uint(next_prefix.account_id_prefix, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        vm::CellBuilder cb;
        CHECK(cb.store_long_bool(enqueued_lt) && cb.store_ref_bool(rec.out_msg));
        if (!ns_.out_msg_queue_->set_builder(queue_key, cb, vm::Dictionary::SetMode::Add)) {
          return fatal_error("failed to store message to out msg queue for msg_export_tr");
        }
        ++ns_.out_msg_queue_size_.value();
        break;
      }
      case block::gen::OutMsg::msg_export_deq_imm: {
        block::gen::OutMsg::Record_msg_export_deq_imm rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.out_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_export_deq_imm");
        }

        auto src_prefix = block::tlb::MsgAddressInt::get_prefix(msg.src);
        auto dest_prefix = block::tlb::MsgAddressInt::get_prefix(msg.dest);
        auto cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.cur_addr);

        td::BitArray<32 + 64 + 256> queue_key;
        td::BitPtr ptr = queue_key.bits();
        ptr.store_int(cur_prefix.workchain, 32);
        ptr.advance(32);
        ptr.store_uint(cur_prefix.account_id_prefix, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        if (ns_.out_msg_queue_->lookup_delete(queue_key).is_null()) {
          return fatal_error("failed to delete message from out msg queue for msg_export_deq_imm");
        }
        --ns_.out_msg_queue_size_.value();
        break;
      }
      case block::gen::OutMsg::msg_export_new_defer: {
        block::gen::OutMsg::Record_msg_export_new_defer rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        CHECK(block::gen::csr_unpack(value, rec));
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.out_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_export_new");
        }
        LogicalTime lt = msg.created_lt;
        WorkchainId wc;
        StdSmcAddress addr;
        if (!block::tlb::t_MsgAddressInt.extract_std_address(msg.src, wc, addr)) {
          return fatal_error("failed to extract src address for msg_export_new_defer");
        }

        vm::Dictionary dispatch_dict{64};
        td::uint64 dispatch_dict_size;
        if (!block::unpack_account_dispatch_queue(ns_.dispatch_queue_->lookup(addr), dispatch_dict,
                                                  dispatch_dict_size)) {
          return fatal_error(PSTRING() << "cannot unpack AccountDispatchQueue for account " << addr.to_hex());
        }
        td::BitArray<64> key;
        key.store_ulong(lt);
        vm::CellBuilder cb;
        CHECK(cb.store_long_bool(lt) && cb.store_ref_bool(rec.out_msg));
        if (!dispatch_dict.set_builder(key, cb, vm::Dictionary::SetMode::Add)) {
          return fatal_error(PSTRING() << "cannot add message to AccountDispatchQueue for account " << addr.to_hex()
                                       << ", lt=" << lt);
        }
        ++dispatch_dict_size;
        ns_.dispatch_queue_->set(addr, block::pack_account_dispatch_queue(dispatch_dict, dispatch_dict_size));
        break;
      }
      case block::gen::OutMsg::msg_export_deferred_tr: {
        block::gen::OutMsg::Record_msg_export_deferred_tr rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.out_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_export_deferred_tr");
        }
        if (!env.emitted_lt) {
          return fatal_error("no emitted_lt in msg_export_deferred_tr");
        }
        LogicalTime enqueued_lt = env.emitted_lt.value();

        auto src_prefix = block::tlb::MsgAddressInt::get_prefix(msg.src);
        auto dest_prefix = block::tlb::MsgAddressInt::get_prefix(msg.dest);
        auto next_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.next_addr);

        td::BitArray<32 + 64 + 256> queue_key;
        td::BitPtr ptr = queue_key.bits();
        ptr.store_int(next_prefix.workchain, 32);
        ptr.advance(32);
        ptr.store_uint(next_prefix.account_id_prefix, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        vm::CellBuilder cb;
        CHECK(cb.store_long_bool(enqueued_lt) && cb.store_ref_bool(rec.out_msg));
        if (!ns_.out_msg_queue_->set_builder(queue_key, cb, vm::Dictionary::SetMode::Add)) {
          return fatal_error("failed to store message to out msg queue for msg_export_deferred_tr");
        }
        ++ns_.out_msg_queue_size_.value();
        break;
      }
      case block::gen::OutMsg::msg_export_deq: {
        return fatal_error("msg_export_deq are deprecated");
      }
      case block::gen::OutMsg::msg_export_deq_short: {
        block::gen::OutMsg::Record_msg_export_deq_short rec;
        CHECK(block::gen::csr_unpack(value, rec));
        td::BitArray<32 + 64 + 256> queue_key;
        td::BitPtr ptr = queue_key.bits();
        ptr.store_int(rec.next_workchain, 32);
        ptr.advance(32);
        ptr.store_uint(rec.next_addr_pfx, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        if (ns_.out_msg_queue_->lookup_delete(queue_key).is_null()) {
          return fatal_error("cannot delete from out msg queue");
        }
        --ns_.out_msg_queue_size_.value();
        break;
      }
      case block::gen::OutMsg::msg_export_tr_req: {
        block::gen::OutMsg::Record_msg_export_tr_req rec;
        block::tlb::MsgEnvelope::Record_std env;
        block::gen::CommonMsgInfo::Record_int_msg_info msg;
        if (!block::gen::csr_unpack(value, rec) || !block::tlb::unpack_cell(rec.out_msg, env) ||
            !block::gen::csr_unpack_inexact(vm::load_cell_slice_ref(env.msg), msg)) {
          return fatal_error("cannot unpack msg_export_tr_rec");
        }
        LogicalTime enqueued_lt = start_lt_;

        auto src_prefix = block::tlb::MsgAddressInt::get_prefix(msg.src);
        auto dest_prefix = block::tlb::MsgAddressInt::get_prefix(msg.dest);
        auto cur_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.cur_addr);
        auto next_prefix = block::interpolate_addr(src_prefix, dest_prefix, env.next_addr);

        td::BitArray<32 + 64 + 256> queue_key;

        td::BitPtr ptr = queue_key.bits();
        ptr.store_int(cur_prefix.workchain, 32);
        ptr.advance(32);
        ptr.store_uint(cur_prefix.account_id_prefix, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        if (ns_.out_msg_queue_->lookup_delete(queue_key).is_null()) {
          return fatal_error("failed to delete requeued message from out msg queue");
        }

        ptr.store_int(next_prefix.workchain, 32);
        ptr.advance(32);
        ptr.store_uint(next_prefix.account_id_prefix, 64);
        ptr.advance(64);
        ptr.copy_from(key, 256);
        vm::CellBuilder cb;
        CHECK(cb.store_long_bool(enqueued_lt) && cb.store_ref_bool(rec.out_msg));
        if (!ns_.out_msg_queue_->set_builder(queue_key, cb, vm::Dictionary::SetMode::Add)) {
          return fatal_error("failed to store message to out msg queue for msg_export_tr_req");
        }
        break;
      }
    }
    return true;
  });
  if (!ok) {
    return reject_query("failed to parse out msg dict");
  }
  return true;
}



}  // namespace solution
