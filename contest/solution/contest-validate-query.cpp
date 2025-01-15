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

// The implementation has been split into multiple files:
// - error-ctx.cpp: ErrorCtx related implementations
// - contest-validate-query-init.cpp: Initialization and startup related functions
// - contest-validate-query-state.cpp: State handling functions
// - contest-validate-query-validation.cpp: Validation related functions
// - contest-validate-query-queue.cpp: Message queue related functions
