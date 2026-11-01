#!/bin/bash
# usage: run1g.sh SECS SEED m k r   -> one haar_gen3 run on meta m k r x Z_1, then apsp check if solved
B=/home/user/degree-diameter/research/squads/beyond11b/bin
D=/home/user/degree-diameter/research/squads/beyond11b/r1/g02
S=$1; SEED=$2; m=$3; k=$4; r=$5
tag=m${m}_k${k}_r${r}_s${SEED}
cd $D
THREADS=1 timeout 105 nice -n 10 $B/haar_gen3 4 11 $S $SEED 4 sol_$tag.sol meta $m $k $r 1 > log_$tag.txt 2>&1
res=$(grep RESULT log_$tag.txt | head -1)
echo "$tag | $res"
if grep -q "best=0 " log_$tag.txt; then
  timeout 60 nice -n 10 $B/apsp <(timeout 60 python3 /home/user/degree-diameter/research/frontier/build_haar2.py sol_$tag.sol edges_$tag.txt >/dev/null 2>&1; cat edges_$tag.txt) 4 11 2>&1 | tail -1 | sed "s/^/   apsp $tag: /"
fi
