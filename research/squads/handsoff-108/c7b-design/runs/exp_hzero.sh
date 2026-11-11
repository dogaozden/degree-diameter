#!/bin/bash
# matching-only annealing (hexagon voltages 0), q given, m list
cd /home/user/degree-diameter/research/squads/handsoff-108/c7b-design
q=$1; shift
for m in "$@"; do
  SEED=$((108851 + m)) HZERO=1 M=$m ITERS=${ITERS:-8000} TEMP0=${TEMP0:-1.0} TEMP1=${TEMP1:-0.05} OUT=runs/hz_q${q}_m${m}.sol \
    timeout ${TMO:-900} nice -n 10 ./src/hexeval $q > runs/hz_q${q}_m${m}.out 2> runs/hz_q${q}_m${m}.log
  echo "m=$m $(tail -1 runs/hz_q${q}_m${m}.out)" >> runs/hz_summary_q${q}.txt
done
