#!/bin/bash
# usage: verify_r1.sh NAME...   (group names as in gtab, e.g. meta_33_2_23): min-cost Haar voltages -> lift -> apsp
F=/home/user/degree-diameter/research/squads/r2-chartlift/c6; C=/home/user/degree-diameter/research/theorems/chartlift
cd $C
for g in "$@"; do
  volt=$(EXH=1 timeout 300 nice -n 10 $F/ctrl_exh bases4/k4r1_000.txt $F/gtab/$g.txt $F/c4s2.flags 1 1 | grep '^EXH min_volt=' | sed 's/EXH min_volt=//')
  cost=$(VOLT=$volt timeout 300 nice -n 10 $F/ctrl_search bases4/k4r1_000.txt $F/gtab/$g.txt $F/c4s2.flags 1 1 $F/lifts/$g | head -1 | sed 's/.*cost=\([0-9]*\).*/\1/')
  m=$(head -1 $F/lifts/$g.ctrl)
  timeout 300 nice -n 10 python3 lift.py $F/lifts/$g.ctrl charts/c4s2_k4_q2.txt 2 4 $F/lifts/$g.edges > /dev/null
  res=$(timeout 600 nice -n 10 $F/apsp $F/lifts/$g.edges 8 5 | tr '\n' ' ')
  rm -f $F/lifts/$g.edges
  echo "$g m=$m cost=$cost volt=$volt :: $res"
done
