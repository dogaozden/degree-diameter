#!/bin/bash
# Z_p lifts, D = 7, every prime p >= 17 and every k with 170 <= 2kp <= 248 (bases k+k, k <= 6).
cd "$(dirname "$0")/.."
for pk in "17 5" "17 6" "19 5" "19 6" "23 4" "23 5" "29 3" "29 4" "31 3" "31 4" "37 3" "41 3" "43 2" "47 2" "53 2" "59 2" "61 2" \
          "89 1" "97 1" "101 1" "103 1" "107 1" "109 1" "113 1"; do
  set -- $pk
  if [ "$2" = 1 ]; then B=bases/b1.txt; else B=bases/b$2.txt; fi
  t0=$(date +%s.%N); bin/zplift $1 7 < $B > runs/zp_p$1_k$2.out; t1=$(date +%s.%N)
  echo "p=$1 k=$2 n=$((2*$1*$2)) bases=$(grep -c '^BASE' runs/zp_p$1_k$2.out) searched=$(grep '^BASE' runs/zp_p$1_k$2.out | grep -vc skip) nodes=$(grep '^BASE' runs/zp_p$1_k$2.out | sed -n 's/.*nodes=\([0-9]*\).*/\1/p' | awk '{s+=$1} END{print s+0}') sols=$(grep -c '^SOL' runs/zp_p$1_k$2.out) time=$(echo "$t1 - $t0" | bc)s"
done
