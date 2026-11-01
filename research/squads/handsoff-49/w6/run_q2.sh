#!/bin/bash
# w6 queue 2: more cost-0 bases. (a) other solutions S of meta 71 35 49 (N=2485, n=4970); (b) bases of order 2484 (n=4968)
H=/home/user/degree-diameter/research/squads/handsoff-49
cd $H/w6
while ! grep -q NEXTDONE groups/summary.txt 2>/dev/null; do sleep 2; done
mkdir -p bases
for seed in 11 12 13 14; do
  timeout 100 nice -n 10 $H/tools/haar_tab 4 9 60 $seed 8 bases/mv_$seed.sol meta 71 35 49 1 > bases/log_mv_$seed.txt 2>&1
  echo "meta71_35_49 seed $seed: $(grep RESULT bases/log_mv_$seed.txt | tail -1)" >> bases/summary.txt
done
for c in "69 36 22" "69 36 47" "23 108 22" "46 54 45" "138 18 47" "207 12 22" "36 69 13" "27 92 26"; do
  set -- $c
  timeout 100 nice -n 10 $H/tools/haar_tab 4 9 45 1 8 bases/n2484_$1_$2_$3.sol meta $1 $2 $3 1 > bases/log_n2484_$1_$2_$3.txt 2>&1
  echo "order2484 meta $1 $2 $3: $(grep RESULT bases/log_n2484_$1_$2_$3.txt | tail -1)" >> bases/summary.txt
done
echo Q2DONE >> bases/summary.txt
