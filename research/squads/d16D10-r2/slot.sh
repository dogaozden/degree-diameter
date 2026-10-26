#!/bin/bash
# usage: slot.sh LABEL cmd args...   Waits until one of the heavy-run slots (slots/1.lock .. slots/N.lock, N read from
# slots/N, default 2) is free, then runs cmd while holding it.  Every (16,10) evaluation run must go through this.
D=$(cd "$(dirname "$0")" && pwd)/slots; mkdir -p "$D"; label=$1; shift
while :; do
  NS=$(cat "$D/N" 2>/dev/null || echo 2)
  for i in $(seq 1 "$NS"); do
    exec {fd}>"$D/$i.lock"
    if flock -n "$fd"; then
      echo "$label $(date -u +%T) pid $$" > "$D/$i.who"
      "$@"; rc=$?
      rm -f "$D/$i.who"; flock -u "$fd"; exec {fd}>&-; exit $rc
    fi
    exec {fd}>&-
  done
  sleep 15
done
