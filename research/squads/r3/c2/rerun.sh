#!/bin/bash
# after the batch: rerun every candidate that reached <= 4 with seeds 2 and 3
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
D=/home/user/degree-diameter/research/squads/r3/c2
cd $D
until grep -q ALLDONE anneal5.out; do sleep 5; done
run(){ tag=$1; seed=$2; alpha=$3; shift 3
  if [ -n "$alpha" ]; then export ALPHA=$alpha; else unset ALPHA; fi
  ORBIT="3 3 1" timeout 900 nice -n 10 $B/haar_sym 10 5 300 $seed 8 $D/${tag}_s$seed.txt "$@" > $D/${tag}_s$seed.log 2>&1
  echo "RERUN ${tag}_s$seed $(grep RESULT $D/${tag}_s$seed.log | tail -1)"
}
if grep -q 'agl1 13 cyc x Z_13.*best=[0-4] ' anneal5.out; then run agl13_z13 2 "" prod agl1 13 cyc 13; run agl13_z13 3 "" prod agl1 13 cyc 13; fi
if grep -q 'sl3agl4_7_a136 RESULT.*best=[0-4] ' anneal5.out; then run sl3agl4_7_a136 2 136 prod sl 3 agl1 4 7; run sl3agl4_7_a136 3 136 prod sl 3 agl1 4 7; fi
echo RERUNDONE
