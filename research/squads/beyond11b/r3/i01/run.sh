#!/bin/bash
# usage: run.sh SECS SEED K p k r  -> one haar_gen3 run (plain random S) on meta p k r, d=4 D=11
B=/home/user/degree-diameter/research/squads/beyond11b/bin
D=/home/user/degree-diameter/research/squads/beyond11b/r3/i01
S=$1; SEED=$2; K=$3; m=$4; k=$5; r=$6
tag=m${m}_k${k}_r${r}_K${K}_s${SEED}
cd $D
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 4 11 $S $SEED $K sol_$tag.sol meta $m $k $r 1 > log_$tag.txt 2>&1
res=$(grep RESULT log_$tag.txt | head -1)
echo "$tag | $(head -2 log_$tag.txt | tail -1) | $res"
if grep -q "best=0 " log_$tag.txt; then
  echo "SOLVED $tag: running checker"
  timeout 100 nice -n 10 python3 /home/user/degree-diameter/research/frontier/build_haar2.py sol_$tag.sol edges_$tag.txt 2>&1 | tail -3
fi
