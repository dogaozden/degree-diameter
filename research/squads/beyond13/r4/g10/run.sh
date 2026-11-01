#!/bin/bash
# run.sh TAG SECS SEED "m1 k1 r1" "m2 k2 r2" : haar_gen3 random S on prod meta(m1,k1,r1) x meta(m2,k2,r2), n = 1, d = 4, D = 13
B=/home/user/degree-diameter/research/frontier/beyond13
D=/home/user/degree-diameter/research/squads/beyond13/r4/g10
TAG=$1; SECS=$2; SEED=$3; F1=$4; F2=$5
cd $D && THREADS=1 nice -n 10 timeout 600 $B/bin/haar_gen3 4 13 $SECS $SEED 8 ${TAG}.sol prod meta $F1 meta $F2 1 > ${TAG}.log 2>&1
