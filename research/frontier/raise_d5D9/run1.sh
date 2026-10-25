#!/bin/bash
# usage: run1.sh SECS SEED K "GROUP... n"   -> sols/<tag>.txt on success, runs/<tag>.log
cd "$(dirname "$0")"
secs=$1; seed=$2; K=$3; grp=$4
tag=$(echo "d5D9_${grp}_s${seed}" | tr ' ' '_')
nice -n 5 timeout $((secs + 60)) env THREADS=1 ./haar_gen3_bin 5 9 $secs $seed $K "sols/$tag.txt" $grp > "runs/$tag.log" 2>&1
echo "$(date +%T) $tag: $(grep RESULT runs/$tag.log)"
