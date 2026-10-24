#!/bin/bash
# gate_opus.sh SECS CMD...: like gate.sh, but uses the Opus session's reserved slots slots/opus<k>.lock, k < R
# (R read from slots/R, default 1). The squad's gate.sh uses slot0..slot(P-1); P + R <= 4 keeps the machine at 4 heavy runs.
D=$(cd "$(dirname "$0")" && pwd)/slots; mkdir -p "$D"
SECS=$1; shift
while true; do
  R=1; [ -s "$D/R" ] && R=$(cat "$D/R")
  for ((k = 0; k < R; k++)); do
    exec 9>>"$D/opus$k.lock"
    if flock -n 9; then
      echo "$(date +%T) take opus$k pid $$: $*" >> "$D/usage.log"
      nice -n 5 timeout "$SECS" "$@"; rc=$?
      echo "$(date +%T) free opus$k pid $$ rc=$rc" >> "$D/usage.log"
      exit $rc
    fi
    exec 9>&-
  done
  sleep 5
done
