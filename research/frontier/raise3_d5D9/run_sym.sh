#!/bin/bash
# one job line "seed|meta m k r"; env SECS (seconds), K (candidates per move), BIN (haar_sym binary).
# Writes runs/<tag>.log; on a solve, copies the solution to research/frontier/sols/ as d5D9_meta_m_k_r_s<seed>_n<graph order>.txt
cd "$(dirname "$0")"
seed=${1%%|*}; grp=${1#*|}
tag=d5D9_$(echo "$grp" | tr ' ' '_')_s${seed}
rm -f "runs/$tag.out"
nice -n 5 timeout $((SECS + 60)) env THREADS=1 "$BIN" 5 9 "$SECS" "$seed" "$K" "runs/$tag.out" $grp 1 > "runs/$tag.log" 2>&1
res=$(grep RESULT "runs/$tag.log")
echo "$(date +%T) $tag: $res"
if [ -f "runs/$tag.out" ]; then
  N=$(echo "$res" | grep -o "N=[0-9]*" | cut -d= -f2)
  name=d5D9_$(echo "$grp" | tr ' ' '_')_s${seed}_n$((2 * N)).txt
  cp "runs/$tag.out" "../../sols/$name"
  echo "$(date +%T) SOLVED $name"
fi
