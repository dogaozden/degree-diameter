#!/bin/bash
# gate.sh SECS CMD [ARGS...]: run CMD under `nice -n 10 timeout SECS` as soon as one of the shared CPU slots is free.
# The machine has 4 cores and 15 GB shared by the Opus session and every squad card, so EVERY heavy process of the
# round (haar_sym / haar_fast runs, RANDORB screens, checkers, long scripts) goes through this gate.
# Slots are flock files slots/slot<k>.lock, k < P; P is read from slots/P (default 4) on every try.
# A slot is also refused while MemAvailable < 3 GB.  Usage is logged to slots/usage.log.
# Example: ./gate.sh 900 env ORBIT="5 2 1" ORBW=5 ../../../research/structured/haar_sym 11 10 840 1 8 out.txt psl 101 151
D=$(cd "$(dirname "$0")" && pwd)/slots; mkdir -p "$D"
SECS=$1; shift
while true; do
  P=4; [ -s "$D/P" ] && P=$(cat "$D/P")
  avail=$(awk '/MemAvailable/ {print int($2/1048576)}' /proc/meminfo)
  if [ "$avail" -ge 3 ]; then
    for ((k = 0; k < P; k++)); do
      exec 9>>"$D/slot$k.lock"
      if flock -n 9; then
        echo "$(date +%T) take slot$k pid $$: $*" >> "$D/usage.log"
        nice -n 10 timeout "$SECS" "$@"; rc=$?
        echo "$(date +%T) free slot$k pid $$ rc=$rc" >> "$D/usage.log"
        exit $rc
      fi
      exec 9>&-
    done
  fi
  sleep 10
done
