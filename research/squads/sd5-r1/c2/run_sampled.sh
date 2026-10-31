#!/bin/bash
# run_sampled.sh: tabu6 on the SAMPLED (6,0) ALPHA records of each group (sdk record numbers), SECS per run.
cd /home/user/degree-diameter/research/squads/sd5-r1/c2
for pair in "362_1 0" "362_1 2" "364_1 28" "364_1 30" "364_1 34" "364_2 18" "364_2 32" "364_2 34" "366_2 10" "368_1 24" "368_1 32" "368_1 34" "368_21 112" "368_21 124" "368_21 96"; do
  set -- $pair; g=$1; r=$2
  f=ht/g${g}.ht; a=$(./alpha_index.sh $f $r)
  o=out/g${g}_r${r}_a${a}_f6m0.out
  SECS=${SECS:-25} SEED=1 MAXSOL=1 EDGES=cand/g${g}_r${r}_a${a}_f6m0.edges timeout 200 nice -n 15 ./tabu6 $f $a 6 0 > $o 2>&1
  echo "$g rec $r alphaidx $a : $(grep '^END' $o)"
done
