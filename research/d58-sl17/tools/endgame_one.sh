#!/bin/bash
# endgame_one.sh <init_file> <order 1|2> <tag>: exhaustive replacement of 1 or 2 elements of S (s_0 = e fixed)
HERE=/home/user/degree-diameter/research/d58-sl17
INIT=$1; ORD=$2; TAG=$3
INIT=$INIT ENDG=$ORD DUMP=$HERE/runs/endg_${TAG}_dump.txt DUMPMAX=0 \
  $HERE/src/sl17 5 8 0 1 8 $HERE/runs/endg_${TAG}_sol.txt sl 17 1 > $HERE/logs/endg_${TAG}.log 2>&1
