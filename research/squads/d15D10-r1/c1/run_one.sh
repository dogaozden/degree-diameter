#!/bin/bash
# run_one.sh P N: one RANDORB=16 cost screen of SL(2,P) x Z_N at (15,10) (default ORBIT 3 5 0), through the squad lock.
# Prints the ORBIT and RANDORB lines and the seconds the run held the lock (setup + sampling).
P=$1; N=$2
cd /home/user/degree-diameter/research/lowmem || exit 1
flock /tmp/claude-0/squad-heavy.lock bash -c '
  t0=$(date +%s)
  timeout 300 nice -n 10 env RANDORB=16 ./haar_lean 15 10 1 11 8 /dev/null sl "$0" "$1" 2>&1 | grep -E "^ORBIT|^RANDORB"
  echo "held_s=$(( $(date +%s) - t0 ))"
' "$P" "$N"
