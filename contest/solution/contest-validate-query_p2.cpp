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
 * Extracts collated data from a cell.
 *
 * @param croot The root cell containing the collated data.
 * @param idx The index of the root.
 *
 * @returns True if the extraction is successful, false otherwise.
 */
bool ContestValidateQuery::extract_collated_data_from(Ref<vm::Cell> croot, int idx) {
  bool is_special = false;
  auto cs = vm::load_cell_slice_special(croot, is_special);
  if (!cs.is_valid()) {
    return reject_query("cannot load root cell");
  }
  if (is_special) {
    if (cs.special_type() != vm::Cell::SpecialType::MerkleProof) {
      return reject_query("it is a special cell, but not a Merkle proof root");
    }
    auto virt_root = vm::MerkleProof::virtualize(croot, 1);
    if (virt_root.is_null()) {
      return reject_query("invalid Merkle proof");
    }
    RootHash virt_hash{virt_root->get_hash().bits()};
    LOG(DEBUG) << "collated datum # " << idx << " is a Merkle proof with root hash " << virt_hash.to_hex();
    auto ins = virt_roots_.emplace(virt_hash, std::move(virt_root));
    if (!ins.second) {
      return reject_query("Merkle proof with duplicate virtual root hash "s + virt_hash.to_hex());
    }
    return true;
  }
  if (block::gen::t_TopBlockDescrSet.has_valid_tag(cs)) {
    LOG(DEBUG) << "collated datum # " << idx << " is a TopBlockDescrSet";
    if (!block::gen::t_TopBlockDescrSet.validate_upto(10000, cs)) {
      return reject_query("invalid TopBlockDescrSet");
    }
    if (top_shard_descr_dict_) {
      return reject_query("duplicate TopBlockDescrSet in collated data");
    }
    top_shard_descr_dict_ = std::make_unique<vm::Dictionary>(cs.prefetch_ref(), 96);
    return true;
  }
  if (block::gen::t_ExtraCollatedData.has_valid_tag(cs)) {
    LOG(DEBUG) << "collated datum # " << idx << " is an ExtraCollatedData";
    if (!block::gen::unpack(cs, extra_collated_data_)) {
      return reject_query("invalid ExtraCollatedData");
    }
    have_extra_collated_data_ = true;
    return true;
  }
  LOG(INFO) << "collated datum # " << idx << " has unknown type (magic " << cs.prefetch_ulong(32) << "), ignoring";
  return true;
}

/**
 * Extracts collated data from a list of collated roots.
 *
 * @returns True if the extraction is successful, False otherwise.
 */
bool ContestValidateQuery::extract_collated_data() {
  int i = -1;
  for (auto croot : collated_roots_) {
    ++i;
    auto guard = error_ctx_add_guard(PSTRING() << "collated datum #" << i);
    try {
      if (!extract_collated_data_from(croot, i)) {
        return reject_query("cannot unpack collated datum");
      }
    } catch (vm::VmError& err) {
      return reject_query(PSTRING() << "vm error " << err.get_msg());
    } catch (vm::VmVirtError& err) {
      return reject_query(PSTRING() << "virtualization error " << err.get_msg());
    }
  }
  if (!have_extra_collated_data_) {
    return reject_query("no extra collated data");
  }
  return true;
}

/**
 * Callback function called after retrieving the masterchain state referenced int the block.
 *
 * @param res The result of the masterchain state retrieval.
 */
void ContestValidateQuery::after_get_mc_state(td::Result<Ref<ShardState>> res) {
  LOG(INFO) << "in ContestValidateQuery::after_get_mc_state() for " << mc_blkid_.to_str();
  --pending;
  if (res.is_error()) {
    fatal_error(res.move_as_error());
    return;
  }
  if (!process_mc_state(Ref<MasterchainState>(res.move_as_ok()))) {
    fatal_error("cannot process masterchain state for "s + mc_blkid_.to_str());
    return;
  }
  if (!pending) {
    if (!try_validate()) {
      fatal_error("cannot validate new block");
    }
  }
}

/**
 * Callback function called after retrieving the shard state for a previous block.
 *
 * @param idx The index of the previous block (0 or 1).
 * @param res The result of the shard state retrieval.
 */
void ContestValidateQuery::after_get_shard_state(int idx, td::Result<Ref<ShardState>> res) {
  LOG(INFO) << "in ContestValidateQuery::after_get_shard_state(" << idx << ")";
  --pending;
  if (res.is_error()) {
    fatal_error(res.move_as_error());
    return;
  }
  // got state of previous block #i
  CHECK((unsigned)idx < prev_blocks.size());
  prev_states.at(idx) = res.move_as_ok();
  CHECK(prev_states[idx].not_null());
  CHECK(prev_states[idx]->get_shard() == ShardIdFull(prev_blocks[idx]));
  CHECK(prev_states[idx]->root_cell().not_null());
  if (!pending) {
    if (!try_validate()) {
      fatal_error("cannot validate new block");
    }
  }
}

/**
 * Processes the retreived masterchain state.
 *
 * @param mc_state The reference to the masterchain state.
 *
 * @returns True if the masterchain state is successfully processed, false otherwise.
 */
bool ContestValidateQuery::process_mc_state(Ref<MasterchainState> mc_state) {
  if (mc_state.is_null()) {
    return fatal_error("could not obtain reference masterchain state "s + mc_blkid_.to_str());
  }
  if (mc_state->get_block_id() != mc_blkid_) {
    if (ShardIdFull(mc_blkid_) != ShardIdFull(mc_state->get_block_id()) || mc_blkid_.seqno()) {
      return fatal_error("reference masterchain state for "s + mc_blkid_.to_str() + " is in fact for different block " +
                         mc_state->get_block_id().to_str());
    }
  }
  mc_state_ = Ref<MasterchainStateQ>(std::move(mc_state));
  mc_state_root_ = mc_state_->root_cell();
  if (mc_state_root_.is_null()) {
    return fatal_error(-666, "unable to load reference masterchain state "s + mc_blkid_.to_str());
  }
  if (!try_unpack_mc_state()) {
    return fatal_error(-666, "cannot unpack reference masterchain state "s + mc_blkid_.to_str());
  }
  return register_mc_state(mc_state_);
}

/**
 * Tries to unpack the masterchain state and perform necessary checks.
 *
 * @returns True if the unpacking and checks are successful, false otherwise.
 */
bool ContestValidateQuery::try_unpack_mc_state() {
  LOG(DEBUG) << "unpacking reference masterchain state";
  auto guard = error_ctx_add_guard("unpack last mc state");
  try {
    if (mc_state_.is_null()) {
      return fatal_error(-666, "no previous masterchain state present");
    }
    mc_state_root_ = mc_state_->root_cell();
    if (mc_state_root_.is_null()) {
      return fatal_error(-666, "latest masterchain state does not have a root cell");
    }
    auto res = block::ConfigInfo::extract_config(
        mc_state_root_, block::ConfigInfo::needShardHashes | block::ConfigInfo::needLibraries |
                            block::ConfigInfo::needValidatorSet | block::ConfigInfo::needWorkchainInfo |
                            block::ConfigInfo::needStateExtraRoot | block::ConfigInfo::needCapabilities |
                            block::ConfigInfo::needPrevBlocks);
    if (res.is_error()) {
      return fatal_error(-666, "cannot extract configuration from reference masterchain state "s + mc_blkid_.to_str() +
                                   " : " + res.move_as_error().to_string());
    }
    config_ = res.move_as_ok();
    CHECK(config_);
    config_->set_block_id_ext(mc_blkid_);
    ihr_enabled_ = config_->ihr_enabled();
    create_stats_enabled_ = config_->create_stats_enabled();
    if (config_->has_capabilities() && (config_->get_capabilities() & ~supported_capabilities())) {
      LOG(INFO) << "block generation capabilities " << config_->get_capabilities()
                   << " have been enabled in global configuration, but we support only " << supported_capabilities()
                   << " (upgrade validator software?)";
    }
    if (config_->get_global_version() > supported_version()) {
      LOG(INFO) << "block version " << config_->get_global_version()
                   << " have been enabled in global configuration, but we support only " << supported_version()
                   << " (upgrade validator software?)";
    }

    old_shard_conf_ = std::make_unique<block::ShardConfig>(*config_);
    new_shard_conf_ = std::make_unique<block::ShardConfig>(*config_);
    if (global_id_ != config_->get_global_blockchain_id()) {
      return reject_query(PSTRING() << "blockchain global id mismatch: new block has " << global_id_
                                    << " while the masterchain configuration expects "
                                    << config_->get_global_blockchain_id());
    }
    if (vert_seqno_ != config_->get_vert_seqno()) {
      return reject_query(PSTRING() << "vertical seqno mismatch: new block has " << vert_seqno_
                                    << " while the masterchain configuration expects " << config_->get_vert_seqno());
    }
    prev_key_block_exists_ = config_->get_last_key_block(prev_key_block_, prev_key_block_lt_);
    if (prev_key_block_exists_) {
      prev_key_block_seqno_ = prev_key_block_.seqno();
    } else {
      prev_key_block_seqno_ = 0;
    }
    if (prev_key_seqno_ != prev_key_block_seqno_) {
      return reject_query(PSTRING() << "previous key block seqno value in candidate block header is " << prev_key_seqno_
                                    << " while the correct value corresponding to reference masterchain state "
                                    << mc_blkid_.to_str() << " is " << prev_key_block_seqno_);
    }
    auto limits = config_->get_block_limits(false);
    if (limits.is_error()) {
      return fatal_error(limits.move_as_error());
    }
    block_limits_ = limits.move_as_ok();
    block_limits_->start_lt = start_lt_;
    block_limit_status_ = std::make_unique<block::BlockLimitStatus>(*block_limits_);
    if (!fetch_config_params()) {
      return false;
    }
    if (!check_this_shard_mc_info()) {
      return fatal_error("masterchain configuration does not admit creating block "s + id_.to_str());
    }
    store_out_msg_queue_size_ = config_->has_capability(ton::capStoreOutMsgQueueSize);
    msg_metadata_enabled_ = config_->has_capability(ton::capMsgMetadata);
    deferring_messages_enabled_ = config_->has_capability(ton::capDeferMessages);
  } catch (vm::VmError& err) {
    return fatal_error(-666, err.get_msg());
  } catch (vm::VmVirtError& err) {
    return fatal_error(-666, err.get_msg());
  }
  return true;
}

/**
 * Fetches and validates configuration parameters from the masterchain configuration.
 * Almost the same as in Collator.
 *
 * @returns True if all configuration parameters were successfully fetched and validated, false otherwise.
 */
bool ContestValidateQuery::fetch_config_params() {
  old_mparams_ = config_->get_config_param(9);
  {
    auto res = config_->get_storage_prices();
    if (res.is_error()) {
      return fatal_error(res.move_as_error());
    }
    storage_prices_ = res.move_as_ok();
  }
  {
    // recover (not generate) rand seed from block header
    CHECK(!rand_seed_.is_zero());
  }
  block::SizeLimitsConfig size_limits;
  {
    auto res = config_->get_size_limits_config();
    if (res.is_error()) {
      return fatal_error(res.move_as_error());
    }
    size_limits = res.move_as_ok();
  }
  {
    // compute compute_phase_cfg / storage_phase_cfg
    auto cell = config_->get_config_param(21);
    if (cell.is_null()) {
      return fatal_error("cannot fetch current gas prices and limits from masterchain configuration");
    }
    if (!compute_phase_cfg_.parse_GasLimitsPrices(std::move(cell), storage_phase_cfg_.freeze_due_limit,
                                                  storage_phase_cfg_.delete_due_limit)) {
      return fatal_error("cannot unpack current gas prices and limits from masterchain configuration");
    }
    auto mc_gas_prices = config_->get_gas_limits_prices(true);
    if (mc_gas_prices.is_error()) {
      return fatal_error(mc_gas_prices.move_as_error_prefix("cannot unpack masterchain gas prices and limits: "));
    }
    compute_phase_cfg_.mc_gas_prices = mc_gas_prices.move_as_ok();
    compute_phase_cfg_.special_gas_full = config_->get_global_version() >= 5;
    storage_phase_cfg_.enable_due_payment = config_->get_global_version() >= 4;
    storage_phase_cfg_.global_version = config_->get_global_version();
    compute_phase_cfg_.block_rand_seed = rand_seed_;
    compute_phase_cfg_.libraries = std::make_unique<vm::Dictionary>(config_->get_libraries_root(), 256);
    compute_phase_cfg_.max_vm_data_depth = size_limits.max_vm_data_depth;
    compute_phase_cfg_.global_config = config_->get_root_cell();
    compute_phase_cfg_.global_version = config_->get_global_version();
    if (compute_phase_cfg_.global_version >= 4) {
      auto prev_blocks_info = config_->get_prev_blocks_info();
      if (prev_blocks_info.is_error()) {
        return fatal_error(
            prev_blocks_info.move_as_error_prefix("cannot fetch prev blocks info from masterchain configuration: "));
      }
      compute_phase_cfg_.prev_blocks_info = prev_blocks_info.move_as_ok();
    }
    if (compute_phase_cfg_.global_version >= 6) {
      compute_phase_cfg_.unpacked_config_tuple = config_->get_unpacked_config_tuple(now_);
    }
    compute_phase_cfg_.suspended_addresses = config_->get_suspended_addresses(now_);
    compute_phase_cfg_.size_limits = size_limits;
    compute_phase_cfg_.precompiled_contracts = config_->get_precompiled_contracts_config();
    compute_phase_cfg_.allow_external_unfreeze = compute_phase_cfg_.global_version >= 8;
  }
  {
    // compute action_phase_cfg
    block::gen::MsgForwardPrices::Record rec;
    auto cell = config_->get_config_param(24);
    if (cell.is_null() || !tlb::unpack_cell(std::move(cell), rec)) {
      return fatal_error("cannot fetch masterchain message transfer prices from masterchain configuration");
    }
    action_phase_cfg_.fwd_mc =
        block::MsgPrices{rec.lump_price,           rec.bit_price,          rec.cell_price, rec.ihr_price_factor,
                         (unsigned)rec.first_frac, (unsigned)rec.next_frac};
    cell = config_->get_config_param(25);
    if (cell.is_null() || !tlb::unpack_cell(std::move(cell), rec)) {
      return fatal_error("cannot fetch standard message transfer prices from masterchain configuration");
    }
    action_phase_cfg_.fwd_std =
        block::MsgPrices{rec.lump_price,           rec.bit_price,          rec.cell_price, rec.ihr_price_factor,
                         (unsigned)rec.first_frac, (unsigned)rec.next_frac};
    action_phase_cfg_.workchains = &config_->get_workchain_list();
    action_phase_cfg_.bounce_msg_body = (config_->has_capability(ton::capBounceMsgBody) ? 256 : 0);
    action_phase_cfg_.size_limits = size_limits;
    action_phase_cfg_.action_fine_enabled = config_->get_global_version() >= 4;
    action_phase_cfg_.bounce_on_fail_enabled = config_->get_global_version() >= 4;
    action_phase_cfg_.message_skip_enabled = config_->get_global_version() >= 8;
    action_phase_cfg_.disable_custom_fess = config_->get_global_version() >= 8;
    action_phase_cfg_.mc_blackhole_addr = config_->get_burning_config().blackhole_addr;
  }
  {
    // fetch block_grams_created
    auto cell = config_->get_config_param(14);
    if (cell.is_null()) {
      basechain_create_fee_ = masterchain_create_fee_ = td::zero_refint();
    } else {
      block::gen::BlockCreateFees::Record create_fees;
      if (!(tlb::unpack_cell(cell, create_fees) &&
            block::tlb::t_Grams.as_integer_to(create_fees.masterchain_block_fee, masterchain_create_fee_) &&
            block::tlb::t_Grams.as_integer_to(create_fees.basechain_block_fee, basechain_create_fee_))) {
        return fatal_error("cannot unpack BlockCreateFees from configuration parameter #14");
      }
    }
  }
  return true;
}

}  // namespace solution
