#!/bin/bash
# run_slot.sh CMD...: run one heavy command in one of the shared CPU slots (blocks until a slot is free), under nice and
# a 1200 s wall-clock timeout. The number of slots is in .nslots (Opus raises it when its own checks finish).
D=/home/user/degree-diameter/research/squads/d16D7_r2/.slots; mkdir -p $D
while true; do
  NS=$(cat /home/user/degree-diameter/research/squads/d16D7_r2/.nslots 2>/dev/null || echo 2)
  for s in $(seq 1 $NS); do
    exec 9>$D/slot$s
    if flock -n 9; then timeout 1200 nice -n 10 "$@"; rc=$?; flock -u 9; exit $rc; fi
  done
  sleep 5
done
