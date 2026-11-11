#!/bin/sh
# usage: screen.sh P m k r c SECS SEED TAG  (env START optional)
R=/home/user/degree-diameter/research/frontier/raise_small
P=$1; m=$2; k=$3; r=$4; c=$5; SECS=$6; SEED=$7; TAG=$8
python3 $R/tools/gtab.py g_$TAG.tab $m $k $r $c >/dev/null || exit 1
D=11 timeout 100 nice -n 10 $R/bin/salift_s $P g_$TAG.tab 1 $SEED $SECS 10 0.3 s_$TAG.sol > log_$TAG.txt 2>&1
echo "$TAG p=$P N=$((m*k*c)) exit=$? best: $(tail -1 log_$TAG.txt)"
