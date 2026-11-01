#!/bin/bash
# deep1.sh: deepen the PGL(2,11) 2+2 lifts with wtt, one run at a time (6 min each), restarts from the best solution
W=/home/user/degree-diameter/research/squads/handsoff-49/w12
cd $W
run() { # name base group seed TT [init]
  local name=$1 base=$2 grp=$3 seed=$4 tt=$5 init=$6
  if [ -n "$init" ]; then extra="$init"; else extra=""; fi
  nice -n 10 timeout 420 ./wtt bases/$base groups/$grp.bin 9 360 $seed runs/$name 10 20 100 10 $tt $extra > logs/$name.out 2> logs/$name.err
  echo "$name $(grep RESULT logs/$name.out | head -1)" >> logs/deep1_summary.txt
}
run d1_mh2_1_s11 b4_mh2_1.txt pgl11 11 10
run d1_mh2_0_s12 b4_mh2_0.txt pgl11 12 10
run d1_mh2_1_s13 b4_mh2_1.txt pgl11 13 20
echo DONE >> logs/deep1_summary.txt
