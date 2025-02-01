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
#include <chrono>

namespace solution {


using namespace ton;
using namespace ton::validator;

using td::Ref;
using namespace std::literals::string_literals;

/**
 * Checks the validity of transactions for a given account block.
 * NB: may be run in parallel for different accounts
 *
 * @param acc_addr The address of the account.
 * @param acc_blk_root The root of the AccountBlock.
 *
 * @returns True if the account transactions are valid, false otherwise.
 */
bool ContestValidateQuery::check_account_transactions(const StdSmcAddress& acc_addr, Ref<vm::CellSlice> acc_blk_root) {
  std::cout << "check_account_transactions enter" << std::endl;

  auto start_time = std::chrono::high_resolution_clock::now();
  block::gen::AccountBlock::Record acc_blk;
  CHECK(tlb::csr_unpack(std::move(acc_blk_root), acc_blk) && acc_blk.account_addr == acc_addr);
  auto account_p = unpack_account(acc_addr.cbits());
  if (!account_p) {
    return reject_query("cannot unpack old state of account "s + acc_addr.to_hex());
  }
  auto& account = *account_p;
  CHECK(account.addr == acc_addr);
  vm::AugmentedDictionary trans_dict{vm::DictNonEmpty(), std::move(acc_blk.transactions), 64,
                                     block::tlb::aug_AccountTransactions};
  td::BitArray<64> min_trans, max_trans;
  CHECK(trans_dict.get_minmax_key(min_trans).not_null() && trans_dict.get_minmax_key(max_trans, true).not_null());
  std::cout << "check_account_transactions reached here -3 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time).count() << std::endl;

  ton::LogicalTime min_trans_lt = min_trans.to_ulong(), max_trans_lt = max_trans.to_ulong();
  std::cout << "check_account_transactions reached here -3.1 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time).count() << std::endl;

  if (!trans_dict.check_for_each_extra([this, &account, min_trans_lt, max_trans_lt](Ref<vm::CellSlice> value,
                                                                                    Ref<vm::CellSlice> extra,
                                                                                    td::ConstBitPtr key, int key_len) {
        
        auto start_time_1 = std::chrono::high_resolution_clock::now();

        CHECK(key_len == 64);
        ton::LogicalTime lt = key.get_uint(64);
        std::cout << "check_account_transactions reached here -3.3 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time_1).count() << std::endl;

        extra.clear();
        std::cout << "check_account_transactions reached here -3.3 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time_1).count() << std::endl;

        return check_one_transaction(account, lt, value->prefetch_ref(), lt == min_trans_lt, lt == max_trans_lt);
      })) {
    return reject_query("at least one Transaction of account "s + acc_addr.to_hex() + " is invalid");
  }
  std::cout << "check_account_transactions reached here -2 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time).count() << std::endl;

  // See Collator::combine_account_trabsactions
  if (account.total_state->get_hash() != account.orig_total_state->get_hash()) {
    // account changed
    if (account.orig_status == block::Account::acc_nonexist) {
      // account created
      CHECK(account.status != block::Account::acc_nonexist);
      vm::CellBuilder cb;
      if (!(cb.store_ref_bool(account.total_state)             // account_descr$_ account:^Account
            && cb.store_bits_bool(account.last_trans_hash_)    // last_trans_hash:bits256
            && cb.store_long_bool(account.last_trans_lt_, 64)  // last_trans_lt:uint64
            && ns_.account_dict_->set_builder(account.addr, cb, vm::Dictionary::SetMode::Add))) {
        return fatal_error(std::string{"cannot add newly-created account "} + account.addr.to_hex() +
                           " into ShardAccounts");
      }
    } else if (account.status == block::Account::acc_nonexist) {
        std::cout << "check_account_transactions reached here -1 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time).count() << std::endl;
// account deleted
      if (verbosity > 2) {
        std::cerr << "deleting account " << account.addr.to_hex() << " with empty new value ";
        block::gen::t_Account.print_ref(std::cerr, account.total_state);
      }
      if (ns_.account_dict_->lookup_delete(account.addr).is_null()) {
        return fatal_error(std::string{"cannot delete account "} + account.addr.to_hex() + " from ShardAccounts");
      }
    } else {
        std::cout << "check_account_transactions reached here 0 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time).count() << std::endl;
// existing account modified
      if (verbosity > 4) {
        std::cerr << "modifying account " << account.addr.to_hex() << " to ";
        block::gen::t_Account.print_ref(std::cerr, account.total_state);
      }

      vm::CellBuilder cb;
      if (!(cb.store_ref_bool(account.total_state)             // account_descr$_ account:^Account
            && cb.store_bits_bool(account.last_trans_hash_)    // last_trans_hash:bits256
            && cb.store_long_bool(account.last_trans_lt_, 64)  // last_trans_lt:uint64
            && ns_.account_dict_->set_builder(account.addr, cb, vm::Dictionary::SetMode::Replace))) {
        return fatal_error(std::string{"cannot modify existing account "} + account.addr.to_hex() +
                           " in ShardAccounts");
      }
    }
  }

  std::cout << "check_account_transactions reached here 1 at " << std::chrono::duration<double>(std::chrono::high_resolution_clock::now() - start_time).count() << std::endl;

  block::gen::HASH_UPDATE::Record hash_upd;
  if (!tlb::type_unpack_cell(std::move(acc_blk.state_update), block::gen::t_HASH_UPDATE_Account, hash_upd)) {
    return reject_query("cannot extract (HASH_UPDATE Account) from the AccountBlock of "s + account.addr.to_hex());
  }
  block::tlb::ShardAccount::Record old_state, new_state;
  if (!(old_state.unpack(ps_.account_dict_->lookup(account.addr)) &&
        new_state.unpack(ns_.account_dict_->lookup(account.addr)))) {
    return reject_query("cannot extract Account from the ShardAccount of "s + account.addr.to_hex());
  }
  if (hash_upd.old_hash != old_state.account->get_hash().bits()) {
    return reject_query("(HASH_UPDATE Account) from the AccountBlock of "s + account.addr.to_hex() +
                        " has incorrect old hash");
  }
  if (hash_upd.new_hash != new_state.account->get_hash().bits()) {
    return reject_query("(HASH_UPDATE Account) from the AccountBlock of "s + account.addr.to_hex() +
                        " has incorrect new hash");
  }

  auto end_time = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> duration = end_time - start_time;
  std::cout << "check_account_transactions took " << duration.count() << " seconds" << std::endl;
  if (duration.count() > 0.004) {
    std::cout << "************************************************************************** check_account_transactions > 0.004 ******************************************************************************" << std::endl;
  }

  return true;
}

/**
 * Checks all transactions in the account blocks.
 *
 * @returns True if all transactions pass the check, False otherwise.
 */
bool ContestValidateQuery::check_transactions() {
  auto start_time = std::chrono::high_resolution_clock::now();

  LOG(INFO) << "checking all transactions";
  ns_.account_dict_ =
      std::make_unique<vm::AugmentedDictionary>(ps_.account_dict_->get_root(), 256, block::tlb::aug_ShardAccounts);
  bool ok = account_blocks_dict_->check_for_each_extra(
      [this](Ref<vm::CellSlice> value, Ref<vm::CellSlice> extra, td::ConstBitPtr key, int key_len) {
        CHECK(key_len == 256);
        return check_account_transactions(key, std::move(value));
      });

  auto end_time = std::chrono::high_resolution_clock::now();
  std::chrono::duration<double> duration = end_time - start_time;
  std::cout << "check_transactions took " << duration.count() << " seconds" << std::endl;

  return ok;
}

/**
 * Checks the processing order of messages in a block.
 *
 * @returns True if the processing order of messages is valid, false otherwise.
 */
bool ContestValidateQuery::check_message_processing_order() {
  // Old rule: if messages m1 and m2 with the same destination generate transactions t1 and t2,
  // then (m1.created_lt < m2.created_lt) => (t1.lt < t2.lt).
  // New rule:
  // If message was taken from dispatch queue, instead of created_lt use emitted_lt
  std::sort(msg_proc_lt_.begin(), msg_proc_lt_.end());
  for (std::size_t i = 1; i < msg_proc_lt_.size(); i++) {
    auto &a = msg_proc_lt_[i - 1], &b = msg_proc_lt_[i];
    if (std::get<0>(a) == std::get<0>(b) && std::get<2>(a) > std::get<2>(b)) {
      return reject_query(PSTRING() << "incorrect message processing order: transaction (" << std::get<1>(a) << ","
                                    << std::get<0>(a).to_hex() << ") processes message created at logical time "
                                    << std::get<2>(a) << ", but a later transaction (" << std::get<1>(b) << ","
                                    << std::get<0>(a).to_hex()
                                    << ") processes an earlier message created at logical time " << std::get<2>(b));
    }
  }

  // Check that if messages m1 and m2 with the same source have m1.created_lt < m2.created_lt then
  // m1.emitted_lt < m2.emitted_lt.
  std::sort(msg_emitted_lt_.begin(), msg_emitted_lt_.end());
  for (std::size_t i = 1; i < msg_emitted_lt_.size(); i++) {
    auto &a = msg_emitted_lt_[i - 1], &b = msg_emitted_lt_[i];
    if (std::get<0>(a) == std::get<0>(b) && std::get<2>(a) >= std::get<2>(b)) {
      return reject_query(PSTRING() << "incorrect deferred message processing order for sender "
                                    << std::get<0>(a).to_hex() << ": message with created_lt " << std::get<1>(a)
                                    << " has emitted_lt" << std::get<2>(a) << ", but message with created_lt "
                                    << std::get<1>(b) << " has emitted_lt" << std::get<2>(b));
    }
  }
  return true;
}

/**
 * Checks the validity of the new shard state.
 *
 * @returns True if the new state is valid, false otherwise.
 */
bool ContestValidateQuery::check_new_state() {
  // shard_state#9023afe2 global_id:int32 -> checked in unpack_next_state()
  // shard_id:ShardIdent -> checked in unpack_next_state()
  // seq_no:uint32 vert_seq_no:# -> checked in unpack_next_state()
  // gen_utime:uint32 gen_lt:uint64 -> checked in unpack_next_state()
  // min_ref_mc_seqno:uint32
  ton::BlockSeqno my_mc_seqno = mc_seqno_;
  ton::BlockSeqno ref_mc_seqno =
      std::min(std::min(my_mc_seqno, min_shard_ref_mc_seqno_), ns_.processed_upto_->min_mc_seqno());
  ns_.min_ref_mc_seqno_ = ref_mc_seqno;
  // out_msg_queue_info:^OutMsgQueueInfo
  // -> _ out_queue:OutMsgQueue proc_info:ProcessedInfo
  //      ihr_pending:IhrPendingInfo = OutMsgQueueInfo;

  // before_split:(## 1) -> checked in unpack_next_state()
  // accounts:^ShardAccounts -> checked in precheck_account_updates() + other
  // ^[ overload_history:uint64 underload_history:uint64
  ns_.overload_history_ = ((ps_.overload_history_ << 1) | extra_collated_data_.overload);
  ns_.underload_history_ = ((ps_.underload_history_ << 1) | extra_collated_data_.underload);

  if (ns_.overload_history_ & ns_.underload_history_ & 1) {
    return reject_query(
        "lower-order bits both set in the new state's overload_history and underload history (block cannot be both "
        "overloaded and underloaded)");
  }
  if (after_split_ || after_merge_) {
    if ((ns_.overload_history_ | ns_.underload_history_) & ~1ULL) {
      return reject_query(
          "new block is immediately after split or after merge, but the old underload or overload history has not been "
          "cleared");
    }
  } else {
    if ((ns_.overload_history_ ^ (ps_.overload_history_ << 1)) & ~1ULL) {
      return reject_query(PSTRING() << "new overload history " << ns_.overload_history_
                                    << " is not compatible with the old overload history " << ps_.overload_history_);
    }
    if ((ns_.underload_history_ ^ (ps_.underload_history_ << 1)) & ~1ULL) {
      return reject_query(PSTRING() << "new underload history " << ns_.underload_history_
                                    << " is not compatible with the old underload history " << ps_.underload_history_);
    }
  }
  // total_balance:CurrencyCollection
  // total_validator_fees:CurrencyCollection
  block::CurrencyCollection old_total_validator_fees(ps_.total_validator_fees_);
  ns_.total_validator_fees_ = old_total_validator_fees + value_flow_.fees_collected - value_flow_.recovered;
  ns_.total_balance_ = value_flow_.to_next_blk;
  return true;
}

/**
 * Validates the value flow of a block.
 *
 * @returns True if the value flow is valid, False otherwise.
 */
bool ContestValidateQuery::postcheck_value_flow() {
  auto accounts_extra = ns_.account_dict_->get_root_extra();
  block::CurrencyCollection cc;
  if (!(accounts_extra.write().advance(5) && cc.unpack(std::move(accounts_extra)))) {
    return reject_query("cannot unpack CurrencyCollection from the root of new accounts dictionary");
  }
  if (cc != value_flow_.to_next_blk) {
    return reject_query("ValueFlow for "s + id_.to_str() + " declares to_next_blk=" + value_flow_.to_next_blk.to_str() +
                        " but the sum over all accounts present in the new state is " + cc.to_str());
  }

  auto expected_fees =
      value_flow_.fees_imported + value_flow_.created + transaction_fees_ + import_fees_ - fees_burned_;
  if (value_flow_.fees_collected != expected_fees) {
    return reject_query(PSTRING() << "ValueFlow for " << id_.to_str() << " declares fees_collected="
                                  << value_flow_.fees_collected.to_str() << " but the total message import fees are "
                                  << import_fees_ << ", the total transaction fees are " << transaction_fees_.to_str()
                                  << ", creation fee for this block is " << value_flow_.created.to_str()
                                  << ", the total imported fees from shards are " << value_flow_.fees_imported.to_str()
                                  << " and the burned fees are " << fees_burned_.to_str() << " with a total of "
                                  << expected_fees.to_str());
  }
  if (total_burned_ != value_flow_.burned) {
    return reject_query(PSTRING() << "invalid burned in value flow: " << id_.to_str() << " declared "
                                  << value_flow_.burned.to_str() << ", correct value is " << total_burned_.to_str());
  }
  return true;
}

Ref<vm::Cell> ContestValidateQuery::get_virt_state_root(td::Bits256 block_root_hash) {
  auto it = virt_roots_.find(block_root_hash);
  if (it == virt_roots_.end()) {
    return {};
  }
  Ref<vm::Cell> root = it->second;
  block::gen::Block::Record block;
  if (!tlb::unpack_cell(root, block)) {
    return {};
  }
  vm::CellSlice upd_cs{vm::NoVmSpec(), block.state_update};
  if (!(upd_cs.is_special() && upd_cs.prefetch_long(8) == 4  // merkle update
        && upd_cs.size_ext() == 0x20228)) {
    return {};
  }
  return vm::MerkleProof::virtualize_raw(upd_cs.prefetch_ref(1), {0, 1});
}

/**
 * MAIN VALIDATOR FUNCTION (invokes other methods in a suitable order).
 *
 * @returns True if the validation is successful, False otherwise.
 */
bool ContestValidateQuery::try_validate() {
  if (pending) {
    return true;
  }
  try {
    if (!stage_) {
      LOG(INFO) << "try_validate stage 0";
      if (!compute_prev_state()) {
        return fatal_error(-666, "cannot compute previous state");
      }
      if (!request_neighbor_queues()) {
        return fatal_error("cannot request neighbor output queues");
      }
      if (!unpack_prev_state()) {
        return fatal_error("cannot unpack previous state");
      }
      if (!init_next_state()) {
        return fatal_error("cannot unpack previous state");
      }
      if (!check_utime_lt()) {
        return reject_query("creation utime/lt of the new block is invalid");
      }
      if (!prepare_out_msg_queue_size()) {
        return reject_query("cannot request out msg queue size");
      }
      stage_ = 1;
      if (pending) {
        return true;
      }
    }
    LOG(INFO) << "try_validate stage 1";
    LOG(INFO) << "running automated validity checks for block candidate " << id_.to_str();
    if (!block::gen::t_BlockRelaxed.validate_ref(10000000, block_root_)) {
      return reject_query("block "s + id_.to_str() + " failed to pass automated validity checks");
    }
    if (!fix_all_processed_upto()) {
      return fatal_error("cannot adjust all ProcessedUpto of neighbor and previous blocks");
    }
    if (!add_trivial_neighbor()) {
      return fatal_error("cannot add previous block as a trivial neighbor");
    }
    if (!unpack_block_data()) {
      return reject_query("cannot unpack block data");
    }
    if (!precheck_account_transactions()) {
      return reject_query("invalid collection of account transactions in ShardAccountBlocks");
    }
    if (!build_new_message_queue()) {
      return reject_query("cannot build a new message queue");
    }
    if (!precheck_message_queue_update()) {
      return reject_query("invalid OutMsgQueue update");
    }
    if (!unpack_dispatch_queue_update()) {
      return reject_query("invalid DispatchQueue update");
    }
    if (!check_in_msg_descr()) {
      return reject_query("invalid InMsgDescr");
    }
    if (!check_out_msg_descr()) {
      return reject_query("invalid OutMsgDescr");
    }
    if (!check_dispatch_queue_update()) {
      return reject_query("invalid OutMsgDescr");
    }
    if (!check_processed_upto()) {
      return reject_query("invalid ProcessedInfo");
    }
    if (!check_in_queue()) {
      return reject_query("cannot check inbound message queues");
    }
    if (!check_transactions()) {
      return reject_query("invalid collection of account transactions in ShardAccountBlocks");
    }
    if (!postcheck_account_updates()) {
      return reject_query("invalid AccountState update");
    }
    if (!check_message_processing_order()) {
      return reject_query("some messages have been processed by transactions in incorrect order");
    }
    if (!check_new_state()) {
      return reject_query("the header of the new shardchain state is invalid");
    }
    if (!postcheck_value_flow()) {
      return reject_query("new ValueFlow is invalid");
    }
    if (!build_state_update()) {
      return reject_query("cannot build state update");
    }
  } catch (vm::VmError& err) {
    return fatal_error(-666, err.get_msg());
  } catch (vm::VmVirtError& err) {
    return reject_query(err.get_msg());
  }
  finish_query();
  return true;
}

/**
 * Creates a new shard state and generates Merkle update. The serialized update is stored to result_state_update_.
 *
 * @return True on success, False on error.
 */
bool ContestValidateQuery::build_state_update() {
  td::Ref<vm::Cell> msg_q_info;
  {
    vm::CellBuilder cb;
    // out_msg_queue_extra#0 dispatch_queue:DispatchQueue out_queue_size:(Maybe uint48) = OutMsgQueueExtra;
    // ... extra:(Maybe OutMsgQueueExtra)
    if (!(cb.store_long_bool(1, 1) && cb.store_long_bool(0, 4) && ns_.dispatch_queue_->append_dict_to_bool(cb))) {
      return false;
    }
    if (!(cb.store_bool_bool(true) && ns_.out_msg_queue_size_ &&
          cb.store_long_bool(ns_.out_msg_queue_size_.value(), 48))) {
      return false;
    }
    vm::CellSlice maybe_extra = cb.as_cellslice();
    cb.reset();
    bool ok = ns_.out_msg_queue_->append_dict_to_bool(cb)                  // _ out_queue:OutMsgQueue
              && cb.append_cellslice_bool(extra_collated_data_.proc_info)  // proc_info:ProcessedInfo
              && cb.append_cellslice_bool(maybe_extra)                     // extra:(Maybe OutMsgQueueExtra)
              && cb.finalize_to(msg_q_info);
    if (!ok) {
      return false;
    }
  }

  td::Ref<vm::Cell> state_root;
  vm::CellBuilder cb, cb2;

  // See Collator::create_shard_state
  if (!(cb.store_long_bool(0x9023afe2, 32)                     // shard_state#9023afe2
        && cb.store_long_bool(global_id_, 32)                  // global_id:int32
        && block::ShardId{shard_}.serialize(cb)                // shard_id:ShardIdent
        && cb.store_long_bool(id_.seqno(), 32)                 // seq_no:uint32
        && cb.store_long_bool(vert_seqno_, 32)                 // vert_seq_no:#
        && cb.store_long_bool(now_, 32)                        // gen_utime:uint32
        && cb.store_long_bool(ns_.lt_, 64)                     // gen_lt:uint64
        && cb.store_long_bool(ns_.min_ref_mc_seqno_, 32)       // min_ref_mc_seqno:uint32
        && cb.store_ref_bool(msg_q_info)                       // out_msg_queue_info:^OutMsgQueueInfo
        && cb.store_long_bool(before_split_, 1)                // before_split:Bool
        && ns_.account_dict_->append_dict_to_bool(cb2)         // accounts:^ShardAccounts
        && cb.store_ref_bool(cb2.finalize())                   // ...
        && cb2.store_long_bool(ns_.overload_history_, 64)      // ^[ overload_history:uint64
        && cb2.store_long_bool(ns_.underload_history_, 64)     //    underload_history:uint64
        && ns_.total_balance_.store(cb2)                       //  total_balance:CurrencyCollection
        && ns_.total_validator_fees_.store(cb2)                //  total_validator_fees:CurrencyCollection
        && cb2.store_bool_bool(false)                          //    libraries:(HashmapE 256 LibDescr)
        && cb2.store_bool_bool(true) && store_master_ref(cb2)  // master_ref:(Maybe BlkMasterInfo)
        && cb.store_ref_bool(cb2.finalize())                   // ]
        && cb.store_bool_bool(false)                           // custom:(Maybe ^McStateExtra)
        && cb.finalize_to(state_root))) {
    return fatal_error("cannot create new ShardState");
  }

  auto state_update = vm::MerkleUpdate::generate(prev_state_root_, state_root, state_usage_tree_.get());
  if (state_update.is_null()) {
    return fatal_error("failed to generate Merkle update");
  }
  result_state_update_ = vm::std_boc_serialize(state_update).move_as_ok();
  return true;
}

/**
 * Stores BlkMasterInfo (for non-masterchain blocks) in the provided CellBuilder.
 *
 * @param cb The CellBuilder to store the reference in.
 *
 * @returns True if the reference is successfully stored, false otherwise.
 */
bool ContestValidateQuery::store_master_ref(vm::CellBuilder& cb) {
  return cb.store_long_bool(mc_state_->get_logical_time(), 64)  // end_lt:uint64
         && cb.store_long_bool(mc_blkid_.seqno(), 32)           // seq_no:uint32
         && cb.store_bits_bool(mc_blkid_.root_hash)             // root_hash:bits256
         && cb.store_bits_bool(mc_blkid_.file_hash);            // file_hash:bits256
}

}  // namespace solution
