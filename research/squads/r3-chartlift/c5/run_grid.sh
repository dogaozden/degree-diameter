#!/bin/bash
# card c5 grid: (a) INIT=star23 with T0 in {2,4,8} x TAU in {20000,60000}; (b) random start T0=4. One process at a time.
C=/home/user/degree-diameter/research/squads/r3-chartlift/c5
CH=/home/user/degree-diameter/research/theorems/chartlift
INIT=$CH/r3/k5q3_pd_star23.txt
cd $CH
S=20
for T0 in 2 4 8; do for TAU in 20000 60000; do
  S=$((S+1)); tag=a_T${T0}_tau${TAU}
  MOVES=star INIT=$INIT T0=$T0 STALL=60000 TAU=$TAU timeout 900 nice -n 10 $C/chart_anneal3 tables/gf3.txt 5 200 $S 1 100 100 $C/$tag.txt > $C/$tag.log 2>&1
  echo "$tag seed=$S $(tail -n 1 $C/$tag.log) | $(python3 chartflags.py $C/$tag.txt 3 5 $C/$tag.flags 2>&1 | tail -n 1)" >> $C/summary.txt
done; done
S=40; tag=b_rand_T4
MOVES=star T0=4 STALL=60000 TAU=20000 timeout 900 nice -n 10 $C/chart_anneal3 tables/gf3.txt 5 200 $S 1 100 100 $C/$tag.txt > $C/$tag.log 2>&1
echo "$tag seed=$S $(tail -n 1 $C/$tag.log) | $(python3 chartflags.py $C/$tag.txt 3 5 $C/$tag.flags 2>&1 | tail -n 1)" >> $C/summary.txt
echo DONE >> $C/summary.txt
