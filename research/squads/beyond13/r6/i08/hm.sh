#!/bin/bash
# usage: hm.sh d D LABEL m k r SEED SECS [START_FILE] -- hmeta on Z_m x|_r Z_k with card settings (K=8 T0=8 T1=1 REHEAT=400)
B=/home/user/degree-diameter/research/frontier/beyond13
C=/home/user/degree-diameter/research/squads/beyond13/r6/i08
d=$1; D=$2; L=$3; m=$4; k=$5; r=$6; SEED=$7; SECS=$8; START_F=$9
OUT=$C/runs/$L.s$SEED.sol; LOG=$C/runs/$L.s$SEED.log
if [ -n "$START_F" ]; then export START=$START_F; fi
THREADS=1 T0=8 T1=1 REHEAT=400 timeout 105 nice -n 10 $B/meta/hmeta $d $D $SECS $SEED 8 $OUT $m $k $r > $LOG 2>&1
grep RESULT $LOG; tail -1 $LOG
