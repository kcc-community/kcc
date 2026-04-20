// Copyright 2024 The go-ethereum Authors
// This file is part of the go-ethereum library.
//
// The go-ethereum library is free software: you can redistribute it and/or modify
// it under the terms of the GNU Lesser General Public License as published by
// the Free Software Foundation, either version 3 of the License, or
// (at your option) any later version.
//
// The go-ethereum library is distributed in the hope that it will be useful,
// but WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
// GNU Lesser General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public License
// along with the go-ethereum library. If not, see <http://www.gnu.org/licenses/>.

package pruner

import (
	"errors"
	"fmt"
	"time"

	"github.com/ethereum/go-ethereum/common"
	"github.com/ethereum/go-ethereum/core/rawdb"
	"github.com/ethereum/go-ethereum/ethdb"
	"github.com/ethereum/go-ethereum/log"
	"github.com/ethereum/go-ethereum/params"
)

// MinBlockAmountReserved is the minimum number of recent blocks that must be
// retained when performing offline block pruning.
//
// The KCC POSA engine reconstructs the validator snapshot by walking headers
// backward from the current head. In the worst case it walks back up to
// params.FullImmutabilityThreshold (90,000) headers before the "trusted
// checkpoint" fallback in consensus/posa/posa.go kicks in. The walker also
// needs to reach the next epoch boundary (epoch=100 on KCC mainnet) after
// accumulating that many headers, so we add a small margin to be safe.
//
// If a user tries to prune more aggressively than this, the validator could
// fail to verify incoming headers after restart, which would stop block
// production. NewBlockPruner rejects any reserved value below this bound.
const MinBlockAmountReserved uint64 = params.FullImmutabilityThreshold + 10000 // 100,000

// BlockPruner is an offline tool that removes historical block data from the
// ancient store (freezer) while keeping the most recent blocks.
//
// Unlike the state pruner, BlockPruner does not need a state snapshot nor a
// bloom filter: it simply advances the freezer tail using the in-place
// TruncateTail primitive provided by rawdb.Freezer. The operation is
// idempotent; running it twice with the same reserved window is a no-op.
//
// BlockPruner is meant for validator nodes and other non-RPC-serving full
// nodes. After pruning, the node cannot answer historical RPC queries for
// blocks below the new tail (eth_getBlockByNumber, eth_getTransactionByHash,
// etc.). It remains fully capable of producing and validating new blocks.
type BlockPruner struct {
	db             ethdb.Database
	amountReserved uint64
}

// NewBlockPruner creates a BlockPruner that will keep the last amountReserved
// blocks in the ancient store. The returned error is non-nil if amountReserved
// is below MinBlockAmountReserved.
func NewBlockPruner(db ethdb.Database, amountReserved uint64) (*BlockPruner, error) {
	if amountReserved < MinBlockAmountReserved {
		return nil, fmt.Errorf(
			"block-amount-reserved %d is below the minimum safe value %d; "+
				"lowering this bound may break KCC consensus (FullImmutabilityThreshold=%d)",
			amountReserved, MinBlockAmountReserved, params.FullImmutabilityThreshold)
	}
	return &BlockPruner{
		db:             db,
		amountReserved: amountReserved,
	}, nil
}

// Prune removes historical block data from the ancient store, keeping only
// the most recent amountReserved blocks. It is safe to call on a database that
// has been pruned before; in that case it only advances the tail further.
//
// The caller is responsible for ensuring that no other process is writing to
// the database while Prune runs (i.e., geth must be stopped).
func (p *BlockPruner) Prune() error {
	start := time.Now()

	// Resolve the current chain head from the key-value store. We use the
	// head header rather than the head block because only the header is
	// guaranteed to be present for all full nodes (the body may be missing
	// on light-ish configurations).
	headHash := rawdb.ReadHeadHeaderHash(p.db)
	if headHash == (common.Hash{}) {
		return errors.New("failed to read head header hash from database")
	}
	headNumber := rawdb.ReadHeaderNumber(p.db, headHash)
	if headNumber == nil {
		return fmt.Errorf("failed to read head header number for hash %s", headHash.Hex())
	}
	head := *headNumber

	// Read the current ancient store state.
	ancients, err := p.db.Ancients()
	if err != nil {
		return fmt.Errorf("failed to read ancients count: %w", err)
	}
	oldTail, err := p.db.Tail()
	if err != nil {
		return fmt.Errorf("failed to read ancient tail: %w", err)
	}

	// The chain must have at least amountReserved blocks for pruning to make
	// any sense. Refuse to touch chains that are too young.
	if head+1 < p.amountReserved {
		return fmt.Errorf(
			"chain head %d is below reserved window %d; nothing to prune",
			head, p.amountReserved)
	}

	// Compute the new tail position. We want to keep the last amountReserved
	// blocks of the chain. Since the most recent blocks are typically still
	// in the kv store (not yet moved to ancient), the tail we can actually
	// advance to is clipped to the number of frozen items.
	newTail := head - p.amountReserved + 1
	if newTail > ancients {
		newTail = ancients
	}

	if newTail <= oldTail {
		log.Info("Nothing to prune; ancient tail already at or ahead of target",
			"currentTail", oldTail,
			"target", newTail,
			"ancients", ancients,
			"head", head)
		return nil
	}

	log.Info("Block pruning plan",
		"head", head,
		"ancients", ancients,
		"currentTail", oldTail,
		"newTail", newTail,
		"blocksToDelete", newTail-oldTail,
		"amountReserved", p.amountReserved)

	// Preserve the genesis block in the kv store before truncating the
	// ancient tail. The freezer's TruncateTail(newTail) hides every item
	// numbered below newTail, including block 0. After such truncation,
	// geth refuses to start with:
	//
	//   Fatal: Failed to register the Ethereum service:
	//   failed to retrieve genesis from ancient out of bounds
	//
	// because the startup code reads genesis via rawdb.ReadBlock(hash, 0)
	// and the ancient lookup returns nothing once tail > 0. The kv-store
	// path is the natural fallback for rawdb readers, so we copy genesis
	// (canonical hash, header, body, total difficulty) back into the kv
	// tables. Receipts are omitted because the genesis block has no
	// transactions.
	//
	// This read must happen before TruncateTail: afterwards, the ancient
	// lookup for block 0 will fail and we would be writing zeroes.
	genesisHash := rawdb.ReadCanonicalHash(p.db, 0)
	if genesisHash == (common.Hash{}) {
		return errors.New("failed to read genesis canonical hash; refusing to truncate")
	}
	genesisHeader := rawdb.ReadHeader(p.db, genesisHash, 0)
	if genesisHeader == nil {
		return fmt.Errorf("failed to read genesis header for %s; refusing to truncate", genesisHash.Hex())
	}
	genesisBody := rawdb.ReadBody(p.db, genesisHash, 0)
	if genesisBody == nil {
		return fmt.Errorf("failed to read genesis body for %s; refusing to truncate", genesisHash.Hex())
	}
	genesisTd := rawdb.ReadTd(p.db, genesisHash, 0)
	if genesisTd == nil {
		return fmt.Errorf("failed to read genesis total difficulty for %s; refusing to truncate", genesisHash.Hex())
	}

	// Perform the in-place tail truncation on the ancient store. This is a
	// local operation that drops data files on disk once the truncated range
	// spans an entire file (2 GiB per file by default), and hides partial
	// files using the freezer's itemHidden metadata. Either way, reads for
	// items below newTail will fail after this call.
	if err := p.db.TruncateTail(newTail); err != nil {
		return fmt.Errorf("failed to truncate ancient tail to %d: %w", newTail, err)
	}
	if err := p.db.Sync(); err != nil {
		return fmt.Errorf("failed to sync ancient store after truncation: %w", err)
	}
	log.Info("Ancient tail truncated", "newTail", newTail, "blocksDeleted", newTail-oldTail)

	// Write genesis back to the kv store. This is idempotent; repeated
	// invocations with the same genesis data simply overwrite the same
	// keys. Placement matters: it must happen after TruncateTail so that
	// genesis survives as the only block below newTail.
	rawdb.WriteCanonicalHash(p.db, genesisHash, 0)
	rawdb.WriteHeader(p.db, genesisHeader)
	rawdb.WriteBody(p.db, genesisHash, 0, genesisBody)
	rawdb.WriteTd(p.db, genesisHash, 0, genesisTd)
	log.Info("Genesis block preserved in kv store", "hash", genesisHash.Hex())

	// Make sure the transaction index tail is not pointing below the new
	// ancient tail. Otherwise, when the node starts with --txlookuplimit,
	// the background indexer would try to walk pruned block bodies and
	// crash.
	if tail := rawdb.ReadTxIndexTail(p.db); tail == nil || *tail < newTail {
		rawdb.WriteTxIndexTail(p.db, newTail)
		log.Info("Updated transaction index tail", "tail", newTail)
	}

	// Run a full-range LevelDB compaction. This is not strictly required for
	// correctness -- the ancient truncation already reclaimed most of the
	// disk space -- but it defragments the LSM tree and releases any lingering
	// tombstones from previous freezer-side operations. Mirrors the tail of
	// snapshot prune-state for consistency.
	log.Info("Compacting database; this may take a while")
	cstart := time.Now()
	for b := 0x00; b <= 0xf0; b += 0x10 {
		var (
			rs = []byte{byte(b)}
			re = []byte{byte(b + 0x10)}
		)
		if b == 0xf0 {
			re = nil
		}
		log.Info("Compacting database",
			"range", fmt.Sprintf("%#x-%#x", rs, re),
			"elapsed", common.PrettyDuration(time.Since(cstart)))
		if err := p.db.Compact(rs, re); err != nil {
			log.Error("Database compaction failed", "err", err)
			return err
		}
	}
	log.Info("Database compaction finished", "elapsed", common.PrettyDuration(time.Since(cstart)))

	log.Info("Block pruning successful",
		"blocksDeleted", newTail-oldTail,
		"newTail", newTail,
		"elapsed", common.PrettyDuration(time.Since(start)))
	return nil
}
