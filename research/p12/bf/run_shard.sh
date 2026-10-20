#!/usr/bin/env bash
# Brute-force cross-check of |LBM(3,8)| (docs/p12-bf-brief.md), one shard = 8 of the MOD = 32 chunks.
# Chunk RES of MOD: genbg generates the connected bipartite cubic graphs on 15+15 vertices in that chunk,
# labelg puts them in plain canonical form, lbm keeps the local bipartite Moore graphs.
# Only the hits are stored; the canonical stream is discarded.
# Usage: scripts/guarded.sh 5 research/p12/bf/run_shard.sh SHARD
# Needs genbg, labelg (nauty) on PATH and research/p12/lbm built from lbm.c.
set -u
SHARD=$1
MOD=32
N=15
ROOT=$(cd "$(dirname "$0")/../../.." && pwd)
OUT=$ROOT/research/p12/bf/$SHARD
LBM=$ROOT/research/p12/lbm
mkdir -p "$OUT/logs"

chunk() {
  local res=$1 t0 t1
  t0=$(date +%s)
  genbg -c $N $N -d3:3 -D3:3 "$res/$MOD" 2> "$OUT/logs/genbg_$res.log" \
    | labelg -q \
    | "$LBM" 3 8 > "$OUT/hits_$res.txt" 2> "$OUT/logs/lbm_$res.log"
  t1=$(date +%s)
  echo "$((t1 - t0))" > "$OUT/logs/time_$res.txt"
}

summary() {
  local k res gen hits secs status tot_gen=0 tot_hits=0 tot_secs=0
  {
    echo "# Shard $SHARD: brute-force cross-check of |LBM(3,8)|"
    echo
    echo "Chunks RES = $((SHARD * 8)) .. $((SHARD * 8 + 7)) of MOD = $MOD; \`genbg -c $N $N -d3:3 -D3:3 RES/$MOD\`, then \`labelg -q\`, then \`lbm 3 8\`."
    echo
    echo "| chunk | graphs generated | LBM hits | runtime (s) | status |"
    echo "|---|---|---|---|---|"
    for k in $(seq 0 7); do
      res=$((SHARD * 8 + k))
      gen=$(sed -n 's/^>Z \([0-9]*\) graphs generated.*/\1/p' "$OUT/logs/genbg_$res.log" 2>/dev/null | tail -1)
      hits=$(wc -l < "$OUT/hits_$res.txt" 2>/dev/null)
      secs=$(cat "$OUT/logs/time_$res.txt" 2>/dev/null)
      if [ -n "$secs" ]; then status=done; else status="not finished"; fi
      [ -n "$gen" ] && tot_gen=$((tot_gen + gen))
      [ -n "$hits" ] && tot_hits=$((tot_hits + hits))
      [ -n "$secs" ] && tot_secs=$((tot_secs + secs))
      echo "| $res/$MOD | ${gen:-?} | ${hits:-?} | ${secs:-?} | $status |"
    done
    echo "| total | $tot_gen | $tot_hits | $tot_secs | |"
    echo
    echo "Hits are graph6 lines with the girth histogram and S1..S3 (see research/p12/lbm.c); per chunk in hits_RES.txt."
  } > "$OUT/summary.md"
}

# Stop switch or time limit: kill this shard's genbg pipelines, keep whatever was finished.
stop() {
  for k in $(seq 0 7); do
    pkill -f "genbg -c $N $N -d3:3 -D3:3 $((SHARD * 8 + k))/$MOD" 2>/dev/null
  done
  summary
  exit 143
}
trap stop TERM INT

for k in $(seq 0 7); do
  chunk $((SHARD * 8 + k)) &
done
wait
summary
echo "shard $SHARD finished"
