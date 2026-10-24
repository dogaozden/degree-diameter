#!/bin/bash
# run_slot.sh CMD...: run one heavy command in one of 3 shared CPU slots (blocks until a slot is free),
# under nice and a 1500 s wall-clock timeout. Every squad card runs its benchmark through this.
D=/home/user/degree-diameter/research/squads/d16D7_r1/.slots; mkdir -p $D
while true; do
  for s in 1 2 3; do
    exec 9>$D/slot$s
    if flock -n 9; then timeout 1500 nice -n 10 "$@"; rc=$?; flock -u 9; exit $rc; fi
  done
  sleep 5
done
