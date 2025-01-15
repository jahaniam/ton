#include "solution.hpp"
#include "vm/boc.h"
#include "block-auto.h"
#include "contest-validate-query.hpp"

void run_contest_solution(ton::BlockIdExt block_id, td::BufferSlice block_data, td::BufferSlice collated_data,
                          td::Promise<td::BufferSlice> promise) {
  // Deserialize block data once and verify basic structure
  TRY_RESULT_PROMISE(promise, root, vm::std_boc_deserialize(block_data));
  if (root.is_null()) {
    return promise.set_error(td::Status::Error("Failed to deserialize block"));
  }

  // Create validation actor - it will start validation automatically
  td::actor::create_actor<solution::ContestValidateQuery>(
      "validate", block_id, std::move(block_data), std::move(collated_data), std::move(promise)).release();
}
