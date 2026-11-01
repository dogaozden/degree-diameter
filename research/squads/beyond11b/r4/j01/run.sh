#!/bin/bash
# usage: run.sh SEED K SPEC...   (one 95 s haar_gen3 run at d=4 D=11; appends to runs.txt)
cd /home/user/degree-diameter/research/squads/beyond11b/r4/j01
B=/home/user/degree-diameter/research/squads/beyond11b/bin
seed=$1; K=$2; shift 2
tag=$(echo "$@" | tr ' ' '_')_s${seed}_K${K}
out=sol_${tag}.txt
log=log_${tag}.txt
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 4 11 95 $seed $K $out "$@" 1 > $log 2>&1
res=$(grep RESULT $log | sed 's/.*best=/best=/')
st=$(grep -c . $log)
echo "seed=$seed K=$K spec=[$*] $res $(date +%H:%M:%S) file=$( [ -f $out ] && echo $out || echo none)" >> runs.txt
echo "seed=$seed K=$K spec=[$*] $res"
