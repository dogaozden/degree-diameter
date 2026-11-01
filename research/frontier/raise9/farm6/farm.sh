#!/bin/bash
# farm.sh (job raise-d9): fresh-seed farm on the (6,9) Frobenius lead Z1559 x|_84 Z41 (N 63,919; r2/f02 reached cost 2 on 1 of
# 10 seeds), plain random S, haar_gen3s, 90 s per seed, K = 8, 1 thread; stops at the first cost-0 solution.
cd "$(dirname "$0")"; B=/home/user/degree-diameter/research/squads/raise9/bin
spec=${SPEC:-"meta 1559 41 84"}; tag=${TAG:-z1559}; s=${S0:-1001}
while true; do
  SAVEBEST=b_${tag}_s$s.txt THREADS=1 nice -n 3 $B/haar_gen3s 6 9 90 $s 8 out_${tag}_s$s.txt $spec 1 > log_${tag}_s$s.txt 2>&1
  r=$(grep -h RESULT log_${tag}_s$s.txt | tail -1); echo "$(date -u +%T) seed $s: $r"
  if [ -s out_${tag}_s$s.txt ]; then echo "SOLVED seed $s"; break; fi
  s=$((s+1))
done
