#!/bin/bash
# run_variant.sh NAME SEED SECS [VAR=value ...]   (c7-throughput: one CPU-clocked, logged run of haar_c7 on psl 23 97)
# Logs: NAME.log (stderr: IM and CHAIN lines), NAME.out (stdout: RESULT). Heavy run: nice 10, one thread, 1.5 GB.
set -u
cd /home/user/degree-diameter/research/squads/handsoff-108/c7-throughput
NAME=$1; SEED=$2; SECS=$3; shift 3
( ulimit -v 1572864
  exec env THREADS=1 CPUCLOCK=1 IMLOG=1 ORBIT="3 3 1" RESTARTAFTER=0 ORBW=3 COOL=15 REHEAT=30 "$@" \
    timeout 4000 nice -n 10 ./haar_c7 10 8 "$SECS" "$SEED" 8 sol_${NAME}.txt psl 23 97 ) > "$NAME.out" 2> "$NAME.log" &
echo "started $NAME pid $!"
