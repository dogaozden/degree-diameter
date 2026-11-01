#!/bin/bash
# usage: run.sh TAG SECS SEED m1 k1 m2 k2 [n]
B=/home/user/degree-diameter/research/frontier/beyond13
D=/home/user/degree-diameter/research/squads/beyond13/r3/f08
TAG=$1; SECS=$2; SEED=$3; m1=$4; k1=$5; m2=$6; k2=$7; n=${8:-1}
r1=$(python3 -c "m=$m1;k=$k1;print(next(r for r in (pow(g,(m-1)//k,m) for g in range(2,m)) if r!=1))")
r2=$(python3 -c "m=$m2;k=$k2;print(next(r for r in (pow(g,(m-1)//k,m) for g in range(2,m)) if r!=1))")
cd $D && THREADS=1 timeout 105 nice -n 10 $B/bin/haar_gen3 5 13 $SECS $SEED 8 ${TAG}.sol prod meta $m1 $k1 $r1 meta $m2 $k2 $r2 $n > ${TAG}.log 2>&1
tail -1 ${TAG}.log
