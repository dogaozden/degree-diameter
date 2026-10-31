#!/bin/bash
# run_batch2.sh: tabu6 on the remaining sampled records (368_23 (4,1); (6,0) on 366_3, 366_4, 368_7).
cd /home/user/degree-diameter/research/squads/sd5-r1/c2
run() { g=$1; r=$2; f=ht/g${g}.ht; a=$(./alpha_index.sh $f $r); m=$3; k=$4
  o=out/g${g}_r${r}_a${a}_f${k}m${m}.out
  SECS=${SECS:-25} SEED=1 MAXSOL=1 EDGES=cand/g${g}_r${r}_a${a}_f${k}m${m}.edges timeout 200 nice -n 15 ./tabu6 $f $a $k $m > $o 2>&1
  echo "$g rec $r alphaidx $a f$k m$m : $(grep '^END' $o)"; }
run 368_23 73 1 4
run 366_3 4 0 6
run 366_3 5 0 6
run 366_4 4 0 6
run 366_4 8 0 6
run 368_7 2 0 6
run 368_7 32 0 6
