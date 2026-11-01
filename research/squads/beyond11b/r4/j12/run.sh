#!/bin/bash
# usage: run.sh SEED K P k R
B=/home/user/degree-diameter/research/squads/beyond11b/bin
cd /home/user/degree-diameter/research/squads/beyond11b/r4/j12
s=$1; K=$2; p=$3; k=$4; r=$5; out=s_${k}_${p}_${s}_K${K}.txt
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 5 11 95 $s $K $out meta $p $k $r 1 > log_${k}_${p}_${s}_K${K}.txt 2>&1
res=$(grep RESULT log_${k}_${p}_${s}_K${K}.txt | sed 's/.*N=/N=/')
echo "$s $K meta $p $k $r n1 $res file=$out" >> runs.txt
echo "$k $p $s K$K: $res"
