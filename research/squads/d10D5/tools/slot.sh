#!/bin/bash
# slot.sh CMD...: run CMD while holding one of 4 machine-wide CPU slots (job cell-10-5), so that the Opus session and
# all squad cards together never run more than 4 heavy processes.  Waits until a slot is free.
D=$(cd "$(dirname "$0")/.." && pwd)/locks; mkdir -p "$D"
while true; do
  for i in 0 1 2 3; do
    exec 9>"$D/slot$i"
    if flock -n 9; then "$@"; rc=$?; flock -u 9; exit $rc; fi
  done
  sleep 3
done
