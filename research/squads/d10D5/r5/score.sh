#!/bin/bash
# score.sh STATE.sol C0.lift2.sol "FDSET": true cost = coset-0 bad pairs + coverage holes (corrected) + D1 holes.
# Prints "SCORE n (coset0, coverage, D1)". If n = 0 it also runs the exact check (finish_fd.sh): success is the line
# "RESULT VALID d=10 D=5 n=4842". Run from anywhere; uses r4/ tools.
R4=/home/user/degree-diameter/research/squads/d10D5/r4
S=$(readlink -f "$1"); C=$(readlink -f "$2"); FS=$3
cd $R4 && out=$(SECS=0 timeout 300 nice -n 5 python3 lns3.py "$S" "$C" "$FS" /dev/null 2>&1 | grep '^start')
echo "SCORE ${out#start }"
n=$(echo "$out" | awk '{print $2}')
if [ "$n" = "0" ]; then T=$(mktemp -d); ./finish_fd.sh "$S" "$C" "$FS" $T/fin | tail -n 1; fi
