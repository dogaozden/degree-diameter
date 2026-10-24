#!/bin/bash
# slot.sh CMD...: run CMD in one of two shared "light" slots (at most 2 squad proxy runs on the box at once).
while true; do
  for i in 1 2; do
    exec 9>/tmp/claude-0/squad-light-$i.lock
    if flock -n 9; then "$@"; rc=$?; flock -u 9; exit $rc; fi
  done
  sleep 2
done
