#!/bin/bash
# heavy.sh SECONDS CMD...: run CMD under `timeout SECONDS nice -n 10`, holding one of NSLOTS machine-wide slots
# (default 3), so that squad cards never run more than NSLOTS heavy jobs at once. Waits for a free slot.
# Usage example: research/squads/bin/heavy.sh 600 ./glift data/gh_3.txt 1 7 540 1 out.txt
T=$1; shift
NSLOTS=${NSLOTS:-3}
LOCKDIR=/tmp/squad_heavy_locks; mkdir -p $LOCKDIR
while true; do
  for i in $(seq 0 $((NSLOTS-1))); do
    exec {fd}>$LOCKDIR/slot$i
    if flock -n $fd; then
      timeout "$T" nice -n 10 "$@"; rc=$?
      flock -u $fd; exec {fd}>&-
      exit $rc
    fi
    exec {fd}>&-
  done
  sleep 5
done
