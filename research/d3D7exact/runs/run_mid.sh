#!/bin/bash
# Z_p lifts, D = 7, p in {11, 13, 17}, bases k+k with k = 7..9.
cd "$(dirname "$0")/.."
S=/tmp/claude-0/-home-user-degree-diameter/12d74605-d8e1-550d-b7fb-3e2ad7b58b29/scratchpad/bases
for pk in "17 7" "13 7" "13 8" "11 8" "13 9" "11 9"; do
  set -- $pk
  B=bases/b$2.txt; [ -f $B ] || B=$S/b$2.txt
  t0=$(date +%s.%N); bin/zplift $1 7 < $B > runs/zp_p$1_k$2.out; t1=$(date +%s.%N)
  echo "p=$1 k=$2 n=$((2*$1*$2)) bases=$(grep -c '^BASE' runs/zp_p$1_k$2.out) searched=$(grep '^BASE' runs/zp_p$1_k$2.out | grep -vc skip) nodes=$(grep '^BASE' runs/zp_p$1_k$2.out | sed -n 's/.*nodes=\([0-9]*\).*/\1/p' | awk '{s+=$1} END{print s+0}') sols=$(grep -c '^SOL' runs/zp_p$1_k$2.out) time=$(echo "$t1 - $t0" | bc)s"
done
