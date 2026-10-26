#!/bin/bash
# anneal.sh TABLE D SECS NSEEDS TAG : plain annealing, seeds 1..NSEEDS, appends RESULT lines to logs/TAG.log
H=/home/user/degree-diameter/research/squads/hunt-d5
T=$1; d=$2; S=$3; N=$4; TAG=$5; mkdir -p logs
for ((s=1; s<=N; s++)); do
  OMP_NUM_THREADS=1 THREADS=1 timeout $((S*3+30)) nice -n 10 $H/tools/haar5 anneal $T $d $S $s tables/x_${TAG}_$s.out 2>/dev/null | grep RESULT | sed "s/^/seed=$s /" >> logs/$TAG.log
done
