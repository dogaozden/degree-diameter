#!/bin/bash
# usage: run.sh LABEL m1 k1 r1 m2 k2 r2 SEED SECS [START_FILE]
# Haar graph of G = (Z_m1 x|_r1 Z_k1) x (Z_m2 x|_r2 Z_k2), d=5, D=11, random S (haar_gen3), one thread.
B=/home/user/degree-diameter/research/frontier/beyond13
H=/home/user/degree-diameter/research/squads/beyond13/r5/h07
L=$1; m1=$2; k1=$3; r1=$4; m2=$5; k2=$6; r2=$7; SEED=$8; SECS=$9; START_F=${10}
OUT=$H/runs/$L.s$SEED.sol
LOG=$H/runs/$L.s$SEED.log
if [ -n "$START_F" ]; then export START=$START_F; fi
THREADS=1 timeout 105 nice -n 10 $B/bin/haar_gen3 5 11 $SECS $SEED 8 $OUT prod meta $m1 $k1 $r1 meta $m2 $k2 $r2 1 > $LOG 2>&1
grep RESULT $LOG
