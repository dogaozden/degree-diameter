#!/usr/bin/env bash
# One chunk of the (3,8) run: connected cubic bipartite graphs on N+N vertices, chunk RES of MOD.
# Pipeline: genbg (bicoloured) -> labelg (plain canonical form, dedupes colour swaps) -> lbm filter.
# Usage: run38.sh N RES MOD OUTDIR
set -u
N=$1; RES=$2; MOD=$3; OUT=$4
BIN=/Users/dogaozden/AI_Projects/degree-diameter/research/p12
mkdir -p "$OUT"
nice -n 15 genbg -q -c "$N" "$N" -d3:3 -D3:3 "$RES/$MOD" \
  | nice -n 15 labelg -q \
  | tee "$OUT/canon_$RES.g6" \
  | nice -n 15 "$BIN/lbm" 3 8 > "$OUT/hits_$RES.txt" 2> "$OUT/lbm_$RES.log"
echo "chunk $RES/$MOD done: $(wc -l < "$OUT/canon_$RES.g6") canonical lines" >> "$OUT/progress.log"
