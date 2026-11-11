#!/bin/bash
# usage: launch_k4.sh SEED SECS GROUP... (n last); ORBIT and extra env passed via environment
cd /home/user/degree-diameter || exit 1
SEED=$1; SECS=$2; shift 2
TAG=$(echo "$*" | tr ' ' '_')
OUT=research/structured/runs/raise_d9D8_r3
env ORBIT="${ORBIT:-4 2 1}" THREADS=1 nice timeout $((SECS+120)) research/structured/haar_sym 9 8 $SECS $SEED 8 $OUT/d9D8_${TAG}_orb4f1_s${SEED}.txt "$@" > $OUT/d9D8_${TAG}_orb4f1_s${SEED}.log 2>&1
