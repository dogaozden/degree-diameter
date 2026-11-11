#!/bin/bash
# usage: run_hm.sh LABEL m k r SEED SECS  -- single metacyclic group Z_m x|_r Z_k, d=5 D=11, hmeta
B=/home/user/degree-diameter/research/frontier/beyond13
H=/home/user/degree-diameter/research/squads/beyond13/r5/h07
L=$1; m=$2; k=$3; r=$4; SEED=$5; SECS=$6; START_F=$7
[ -n "$START_F" ] && export START=$START_F
THREADS=1 timeout 105 nice -n 10 $B/meta/hmeta 5 11 $SECS $SEED 8 $H/runs/$L.s$SEED.sol $m $k $r > $H/runs/$L.s$SEED.log 2>&1
grep -i result $H/runs/$L.s$SEED.log | tail -1; tail -1 $H/runs/$L.s$SEED.log
