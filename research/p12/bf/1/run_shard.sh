#!/usr/bin/env bash
# Brute-force cross-check of |LBM(3,8)| (Problems 1-2), shard SHARD of 1.
# Shard SHARD runs chunks RES = SHARD*8 .. SHARD*8+7 of MOD = 32, 4 at a time (one per core).
# Per chunk: genbg (bicoloured, 15+15 vertices) -> labelg (plain canonical form) -> lbm 3 8 (filter).
# Only the hits are kept; the canonical stream is never stored. Per-chunk counts go to chunk_RES.tsv.
# Usage (from repo root): research/p12/bf/1/run_shard.sh SHARD
set -u
SHARD=$1
MOD=32
ROOT=$(cd "$(dirname "$0")/../../../.." && pwd)
OUT="$ROOT/research/p12/bf/$SHARD"
LBM="$ROOT/research/p12/lbm"
mkdir -p "$OUT/logs"

run_chunk() {
  local res=$1 t0 t1
  t0=$(date +%s)
  set -o pipefail
  genbg -c 15 15 -d3:3 -D3:3 "$res/$MOD" 2> "$OUT/logs/genbg_$res.err" \
    | labelg -q \
    | "$LBM" 3 8 > "$OUT/hits_$res.txt" 2> "$OUT/logs/lbm_$res.log"
  local rc=$?
  t1=$(date +%s)
  # genbg: "> Z <N> graphs generated in <s> sec"; lbm: "... read <N> graphs, LBM hits <H>, ..."
  local gen=$(sed -n 's/^>Z \([0-9]*\) graphs generated.*/\1/p' "$OUT/logs/genbg_$res.err")
  local canon=$(sed -n 's/.*read \([0-9]*\) graphs.*/\1/p' "$OUT/logs/lbm_$res.log")
  local hits=$(sed -n 's/.*LBM hits \([0-9]*\).*/\1/p' "$OUT/logs/lbm_$res.log")
  printf '%s\t%s\t%s\t%s\t%s\t%s\n' "$SHARD" "$res" "${gen:-NA}" "${canon:-NA}" "${hits:-NA}" "$((t1 - t0))" \
    > "$OUT/logs/chunk_$res.tsv"
  echo "chunk $res/$MOD rc=$rc generated=${gen:-NA} canonical=${canon:-NA} hits=${hits:-NA} secs=$((t1 - t0))"
}
export -f run_chunk
export OUT SHARD MOD LBM

first=$((SHARD * 8))
seq "$first" $((first + 7)) | xargs -P 4 -I{} bash -c 'run_chunk {}'
