#!/bin/bash
# usage: step.sh IN.orb OUT_PREFIX SEED GROUP_ARGS... ; env TMAX TMIN TARGP forwarded
B=/home/user/degree-diameter/research/frontier/beyond14/bin/haar_big0
IN=$1; OUT=$2; SEED=$3; shift 3
cd /home/user/degree-diameter/research/squads/beyond14/r5/g10
timeout 105 nice -n 10 env THREADS=1 START=$IN ORBIT="3 2 0" TMAX=${TMAX:-0.5} TMIN=${TMIN:-0.1} TARGP=${TARGP:-90} \
  $B 6 14 85 $SEED 4 $OUT "$@" > $OUT.out 2> $OUT.err
echo "exit=$?"; grep RESULT $OUT.out | cut -c1-120; tail -1 $OUT.err | cut -c1-120
