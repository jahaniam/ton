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
 * Validates and unpacks the value flow of a new block.
 *
 * @param value_flow_root The root of the value flow to be unpacked and validated.
 *
 * @returns True if the value flow is valid and unpacked successfully, false otherwise.
 */
bool ContestValidateQuery::unpack_precheck_value_flow(Ref<vm::Cell> value_flow_root) {
  vm::CellSlice cs{vm::NoVmOrd(), value_flow_root};
  if (!(cs.is_valid() && value_flow_.fetch(cs) && cs.empty_ext())) {
    return reject_query("cannot unpack ValueFlow of the new block "s + id_.to_str());
  }
  std::ostringstream os;
  value_flow_.show(os);
  LOG(DEBUG) << "value flow: " << os.str();
  if (!value_flow_.validate()) {
    LOG(INFO) << "invalid value flow: " << os.str();
    return reject_query("ValueFlow of block "s + id_.to_str() + " is invalid (in-balance is not equal to out-balance)");
  }
  if (!value_flow_.minted.is_zero()) {
    LOG(INFO) << "invalid value flow: " << os.str();
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " is invalid (non-zero minted value in a non-masterchain block)");
  }
  if (!value_flow_.recovered.is_zero()) {
    LOG(INFO) << "invalid value flow: " << os.str();
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " is invalid (non-zero recovered value in a non-masterchain block)");
  }
  if (!value_flow_.burned.is_zero()) {
    LOG(INFO) << "invalid value flow: " << os.str();
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " is invalid (non-zero burned value in a non-masterchain block)");
  }
  if (!value_flow_.recovered.is_zero() && recover_create_msg_.is_null()) {
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " has a non-zero recovered fees value, but there is no recovery InMsg");
  }
  if (value_flow_.recovered.is_zero() && recover_create_msg_.not_null()) {
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " has a zero recovered fees value, but there is a recovery InMsg");
  }
  if (!value_flow_.minted.is_zero() && mint_msg_.is_null()) {
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " has a non-zero minted value, but there is no mint InMsg");
  }
  if (value_flow_.minted.is_zero() && mint_msg_.not_null()) {
    return reject_query("ValueFlow of block "s + id_.to_str() + " has a zero minted value, but there is a mint InMsg");
  }
  if (!value_flow_.minted.is_zero()) {
    block::CurrencyCollection to_mint;
    if (!compute_minted_amount(to_mint) || !to_mint.is_valid()) {
      return reject_query("cannot compute the correct amount of extra currencies to be minted");
    }
    if (value_flow_.minted != to_mint) {
      return reject_query("invalid extra currencies amount to be minted: declared "s + value_flow_.minted.to_str() +
                          ", expected " + to_mint.to_str());
    }
  }
  td::RefInt256 create_fee;
  create_fee = (basechain_create_fee_ >> ton::shard_prefix_length(shard_));
  if (value_flow_.created != block::CurrencyCollection{create_fee}) {
    return reject_query("ValueFlow of block "s + id_.to_str() + " declares block creation fee " +
                        value_flow_.created.to_str() + ", but the current configuration expects it to be " +
                        td::dec_string(create_fee));
  }
  if (!value_flow_.fees_imported.is_zero()) {
    LOG(INFO) << "invalid value flow: " << os.str();
    return reject_query("ValueFlow of block "s + id_.to_str() +
                        " is invalid (non-zero fees_imported in a non-masterchain block)");
  }
  auto accounts_extra = ps_.account_dict_->get_root_extra();
  block::CurrencyCollection cc;
  if (!(accounts_extra.write().advance(5) && cc.unpack(std::move(accounts_extra)))) {
    return reject_query("cannot unpack CurrencyCollection from the root of old accounts dictionary");
  }
  if (cc != value_flow_.from_prev_blk) {
    return reject_query("ValueFlow for "s + id_.to_str() +
                        " declares from_prev_blk=" + value_flow_.from_prev_blk.to_str() +
                        " but the sum over all accounts present in the previous state is " + cc.to_str());
  }
  auto msg_extra = in_msg_dict_->get_root_extra();
  // block::gen::t_ImportFees.print(std::cerr, msg_extra);
  if (!(block::tlb::t_Grams.as_integer_skip_to(msg_extra.write(), import_fees_) && cc.unpack(std::move(msg_extra)))) {
    return reject_query("cannot unpack ImportFees from the augmentation of the InMsgDescr dictionary");
  }
  if (cc != value_flow_.imported) {
    return reject_query("ValueFlow for "s + id_.to_str() + " declares imported=" + value_flow_.imported.to_str() +
                        " but the sum over all inbound messages listed in InMsgDescr is " + cc.to_str());
  }
  if (!cc.unpack(out_msg_dict_->get_root_extra())) {
    return reject_query("cannot unpack CurrencyCollection from the augmentation of the InMsgDescr dictionary");
  }
  if (cc != value_flow_.exported) {
    return reject_query("ValueFlow for "s + id_.to_str() + " declares exported=" + value_flow_.exported.to_str() +
                        " but the sum over all outbound messages listed in OutMsgDescr is " + cc.to_str());
  }
  if (!transaction_fees_.validate_unpack(account_blocks_dict_->get_root_extra())) {
    return reject_query(
        "cannot unpack CurrencyCollection with total transaction fees from the augmentation of the ShardAccountBlocks "
        "dictionary");
  }
  return true;
}

/**
 * Computes the amount of extra currencies to be minted.
 * Similar to Collator::compute_minted_amount()
 *
 * @param to_mint A reference to the CurrencyCollection object to store the minted amount.
 *
 * @returns True if the computation is successful, false otherwise.
 */
bool ContestValidateQuery::compute_minted_amount(block::CurrencyCollection& to_mint) {
  return to_mint.set_zero();
}

bool ContestValidateQuery::postcheck_one_account_update(td::ConstBitPtr acc_id, Ref<vm::CellSlice> old_value,
                                                        Ref<vm::CellSlice> new_value) {
  LOG(DEBUG) << "checking update of account " << acc_id.to_hex(256);
  old_value = ps_.account_dict_->extract_value(std::move(old_value));
  new_value = ns_.account_dict_->extract_value(std::move(new_value));
  auto acc_blk_root = account_blocks_dict_->lookup(acc_id, 256);
  if (acc_blk_root.is_null()) {
    return reject_query("the state of account "s + acc_id.to_hex(256) +
                        " changed in the new state with respect to the old state, but the block contains no "
                        "AccountBlock for this account");
  }
  if (new_value.not_null()) {
    if (!block::tlb::t_ShardAccount.validate_csr(10000, new_value)) {
      return reject_query("new state of account "s + acc_id.to_hex(256) +
                          " failed to pass hand-written validity checks for ShardAccount");
    }
  }
  block::gen::AccountBlock::Record acc_blk;
  block::gen::HASH_UPDATE::Record hash_upd;
  if (!(tlb::csr_unpack(std::move(acc_blk_root), acc_blk) &&
        tlb::type_unpack_cell(std::move(acc_blk.state_update), block::gen::t_HASH_UPDATE_Account, hash_upd))) {
    return reject_query("cannot extract (HASH_UPDATE Account) from the AccountBlock of "s + acc_id.to_hex(256));
  }
  if (acc_blk.account_addr != acc_id) {
    return reject_query("AccountBlock of account "s + acc_id.to_hex(256) + " appears to belong to another account " +
                        acc_blk.account_addr.to_hex());
  }
  Ref<vm::Cell> old_state, new_state;
  if (!(block::tlb::t_ShardAccount.extract_account_state(old_value, old_state) &&
        block::tlb::t_ShardAccount.extract_account_state(new_value, new_state))) {
    return reject_query("cannot extract Account from the ShardAccount of "s + acc_id.to_hex(256));
  }
  if (hash_upd.old_hash != old_state->get_hash().bits()) {
    return reject_query("(HASH_UPDATE Account) from the AccountBlock of "s + acc_id.to_hex(256) +
                        " has incorrect old hash");
  }
  if (hash_upd.new_hash != new_state->get_hash().bits()) {
    return reject_query("(HASH_UPDATE Account) from the AccountBlock of "s + acc_id.to_hex(256) +
                        " has incorrect new hash");
  }
  return true;
}

/**
 * Post-validates all account updates between the old and new state.
 *
 * @returns True if the pre-check is successful, False otherwise.
 */
bool ContestValidateQuery::postcheck_account_updates() {
  LOG(INFO) << "pre-checking all Account updates between the old and the new state";
  try {
    CHECK(ps_.account_dict_ && ns_.account_dict_);
    if (!ps_.account_dict_->scan_diff(
            *ns_.account_dict_,
            [this](td::ConstBitPtr key, int key_len, Ref<vm::CellSlice> old_val_extra,
                   Ref<vm::CellSlice> new_val_extra) {
              CHECK(key_len == 256);
              return postcheck_one_account_update(key, std::move(old_val_extra), std::move(new_val_extra));
            },
            2 /* check augmentation of changed nodes in the new dict */)) {
      return reject_query("invalid ShardAccounts dictionary in the new state");
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid ShardAccount dictionary difference between the old and the new state: "s +
                        err.get_msg());
  }
  return true;
}

/**
 * Pre-validates a single transaction (without actually running it).
 *
 * @param acc_id The 256-bit account address.
 * @param trans_lt The logical time of the transaction.
 * @param trans_csr The cell slice containing the serialized Transaction.
 * @param prev_trans_hash The hash of the previous transaction.
 * @param prev_trans_lt The logical time of the previous transaction.
 * @param prev_trans_lt_len The logical time length of the previous transaction.
 * @param acc_state_hash The hash of the account state before the transaction. Will be set to the hash of the new state.
 *
 * @returns True if the transaction passes pre-checks, false otherwise.
 */
bool ContestValidateQuery::precheck_one_transaction(td::ConstBitPtr acc_id, ton::LogicalTime trans_lt,
                                                    Ref<vm::CellSlice> trans_csr, ton::Bits256& prev_trans_hash,
                                                    ton::LogicalTime& prev_trans_lt, unsigned& prev_trans_lt_len,
                                                    ton::Bits256& acc_state_hash) {
  LOG(DEBUG) << "checking Transaction " << trans_lt;
  if (trans_csr.is_null() || trans_csr->size_ext() != 0x10000) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256) << " is invalid");
  }
  auto trans_root = trans_csr->prefetch_ref();
  block::gen::Transaction::Record trans;
  block::gen::HASH_UPDATE::Record hash_upd;
  if (!(tlb::unpack_cell(trans_root, trans) &&
        tlb::type_unpack_cell(std::move(trans.state_update), block::gen::t_HASH_UPDATE_Account, hash_upd))) {
    return reject_query(PSTRING() << "cannot unpack transaction " << trans_lt << " of " << acc_id.to_hex(256));
  }
  if (trans.account_addr != acc_id || trans.lt != trans_lt) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256)
                                  << " claims to be transaction " << trans.lt << " of " << trans.account_addr.to_hex());
  }
  if (trans.now != now_) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256)
                                  << " claims that current time is " << trans.now
                                  << " while the block header indicates " << now_);
  }
  if (trans.prev_trans_hash != prev_trans_hash || trans.prev_trans_lt != prev_trans_lt) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256)
                                  << " claims that the previous transaction was " << trans.prev_trans_lt << ":"
                                  << trans.prev_trans_hash.to_hex() << " while the correct value is " << prev_trans_lt
                                  << ":" << prev_trans_hash.to_hex());
  }
  if (trans_lt < prev_trans_lt + prev_trans_lt_len) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256)
                                  << " starts at logical time " << trans_lt
                                  << ", earlier than the previous transaction " << prev_trans_lt << " .. "
                                  << prev_trans_lt + prev_trans_lt_len << " ends");
  }
  unsigned lt_len = trans.outmsg_cnt + 1;
  if (trans_lt <= start_lt_ || trans_lt + lt_len > end_lt_) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " .. " << trans_lt + lt_len << " of "
                                  << acc_id.to_hex(256) << " is not inside the logical time interval " << start_lt_
                                  << " .. " << end_lt_ << " of the encompassing new block");
  }
  if (hash_upd.old_hash != acc_state_hash) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256)
                                  << " claims to start from account state with hash " << hash_upd.old_hash.to_hex()
                                  << " while the actual value is " << acc_state_hash.to_hex());
  }
  prev_trans_lt = trans_lt;
  prev_trans_lt_len = lt_len;
  prev_trans_hash = trans_root->get_hash().bits();
  acc_state_hash = hash_upd.new_hash;
  unsigned c = 0;
  vm::Dictionary out_msgs{trans.r1.out_msgs, 15};
  if (!out_msgs.check_for_each([&c](Ref<vm::CellSlice> value, td::ConstBitPtr key, int key_len) {
        CHECK(key_len == 15);
        return key.get_uint(15) == c++;
      }) ||
      c != (unsigned)trans.outmsg_cnt) {
    return reject_query(PSTRING() << "transaction " << trans_lt << " of " << acc_id.to_hex(256)
                                  << " has invalid indices in the out_msg dictionary (keys 0 .. "
                                  << trans.outmsg_cnt - 1 << " expected)");
  }
  return true;
}

// NB: could be run in parallel for different accounts
/**
 * Pre-validates an AccountBlock and all transactions in it.
 *
 * @param acc_id The 256-bit account address.
 * @param acc_blk_root The root of the AccountBlock.
 *
 * @returns True if the AccountBlock passes pre-checks, false otherwise.
 */
bool ContestValidateQuery::precheck_one_account_block(td::ConstBitPtr acc_id, Ref<vm::CellSlice> acc_blk_root) {
  LOG(DEBUG) << "checking AccountBlock for " << acc_id.to_hex(256);
  if (!acc_id.equals(shard_pfx_.bits(), shard_pfx_len_)) {
    return reject_query("new block "s + id_.to_str() + " contains AccountBlock for account " + acc_id.to_hex(256) +
                        " not belonging to the block's shard " + shard_.to_str());
  }
  CHECK(acc_blk_root.not_null());
  // acc_blk_root->print_rec(std::cerr);
  // block::gen::t_AccountBlock.print(std::cerr, acc_blk_root);
  block::gen::AccountBlock::Record acc_blk;
  block::gen::HASH_UPDATE::Record hash_upd;
  if (!(tlb::csr_unpack(acc_blk_root, acc_blk) &&
        tlb::type_unpack_cell(std::move(acc_blk.state_update), block::gen::t_HASH_UPDATE_Account, hash_upd))) {
    return reject_query("cannot extract (HASH_UPDATE Account) from the AccountBlock of "s + acc_id.to_hex(256));
  }
  if (acc_blk.account_addr != acc_id) {
    return reject_query("AccountBlock of account "s + acc_id.to_hex(256) + " appears to belong to another account " +
                        acc_blk.account_addr.to_hex());
  }
  block::tlb::ShardAccount::Record old_state;
  if (!old_state.unpack(ps_.account_dict_->lookup(acc_id, 256))) {
    return reject_query("cannot extract Account from the ShardAccount of "s + acc_id.to_hex(256));
  }
  if (hash_upd.old_hash != old_state.account->get_hash().bits()) {
    return reject_query("(HASH_UPDATE Account) from the AccountBlock of "s + acc_id.to_hex(256) +
                        " has incorrect old hash");
  }
  if (!block::gen::t_AccountBlock.validate_upto(1000000, *acc_blk_root)) {
    return reject_query("AccountBlock of "s + acc_id.to_hex(256) + " failed to pass automated validity checks");
  }
  if (!block::tlb::t_AccountBlock.validate_upto(1000000, *acc_blk_root)) {
    return reject_query("AccountBlock of "s + acc_id.to_hex(256) + " failed to pass hand-written validity checks");
  }
  unsigned last_trans_lt_len = 1;
  ton::Bits256 acc_state_hash = hash_upd.old_hash;
  try {
    vm::AugmentedDictionary trans_dict{vm::DictNonEmpty(), std::move(acc_blk.transactions), 64,
                                       block::tlb::aug_AccountTransactions};
    td::BitArray<64> min_trans, max_trans;
    if (trans_dict.get_minmax_key(min_trans).is_null() || trans_dict.get_minmax_key(max_trans, true).is_null()) {
      return reject_query("cannot extract minimal and maximal keys from the transaction dictionary of account "s +
                          acc_id.to_hex(256));
    }
    if (min_trans.to_ulong() <= start_lt_ || max_trans.to_ulong() >= end_lt_) {
      return reject_query(PSTRING() << "new block contains transactions " << min_trans.to_ulong() << " .. "
                                    << max_trans.to_ulong() << " outside of the block's lt range " << start_lt_
                                    << " .. " << end_lt_);
    }
    if (!trans_dict.validate_check_extra(
            [this, acc_id, &old_state, &last_trans_lt_len, &acc_state_hash](
                Ref<vm::CellSlice> value, Ref<vm::CellSlice> extra, td::ConstBitPtr key, int key_len) {
              CHECK(key_len == 64);
              return precheck_one_transaction(acc_id, key.get_uint(64), std::move(value), old_state.last_trans_hash,
                                              old_state.last_trans_lt, last_trans_lt_len, acc_state_hash) ||
                     reject_query(PSTRING() << "transaction " << key.get_uint(64) << " of account "
                                            << acc_id.to_hex(256) << " is invalid");
            })) {
      return reject_query("invalid transaction dictionary in AccountBlock of "s + acc_id.to_hex(256));
    }
    if (acc_state_hash != hash_upd.new_hash) {
      return reject_query("final state hash mismatch in (HASH_UPDATE Account) for account "s + acc_id.to_hex(256));
    }
  } catch (vm::VmError& err) {
    return reject_query("invalid transaction dictionary in AccountBlock of "s + acc_id.to_hex(256) + " : " +
                        err.get_msg());
  }
  return true;
}



}  // namespace solution
