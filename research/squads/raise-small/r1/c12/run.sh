#!/bin/bash
# run.sh TAG p m k r D SEED SECS [START.best]: salift4 over Z_m x|_r Z_k (one group table per TAG)
RS=/home/user/degree-diameter/research/frontier/raise_small
H=/home/user/degree-diameter/research/squads/raise-small/r1/c12
TAG=$1; p=$2; m=$3; k=$4; r=$5; D=$6; S=$7; SECS=$8; ST=$9
cd $H
[ -f g_$TAG.tab ] || timeout 60 nice -n 10 python3 $RS/tools/gtab.py g_$TAG.tab $m $k $r > /dev/null
if [ -n "$ST" ]; then export START=$ST; fi
D=$D CYC=$SECS timeout 95 nice -n 10 $RS/bin/salift4 $p g_$TAG.tab 1 $S $SECS ${T0:-3} 0.3 s_$TAG.sol >> log_$TAG.txt 2>&1
echo "== $TAG p=$p N=$((m*k)) D=$D seed=$S: $(grep -c . log_$TAG.txt) lines"; tail -2 log_$TAG.txt; head -1 s_$TAG.sol.best 2>/dev/null; ls s_$TAG.sol 2>/dev/null
