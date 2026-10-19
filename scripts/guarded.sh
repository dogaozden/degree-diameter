#!/usr/bin/env bash
# Run a long job under the autopilot rules: a hard time limit, and a stop-switch check every 10 minutes.
# Usage: scripts/guarded.sh HOURS CMD [ARGS...]
# Exit codes: 99 stopped by the switch (scripts/stop_check.sh), 124 hit the time limit, otherwise the job's own code.
# The job gets SIGTERM first (save state on it), then SIGKILL 60 s later.
set -u
hours=$1; shift
here=$(cd "$(dirname "$0")" && pwd)
"$here/stop_check.sh" >/dev/null && { echo "guarded: stop switch is on, not starting" >&2; exit 99; }
"$@" & pid=$!
deadline=$(( $(date +%s) + $(awk "BEGIN{print int($hours*3600)}") ))
next_check=$(( $(date +%s) + 600 ))
stop() {
  kill -TERM "$pid" 2>/dev/null
  for _ in $(seq 60); do kill -0 "$pid" 2>/dev/null || break; sleep 1; done
  kill -KILL "$pid" 2>/dev/null; wait "$pid" 2>/dev/null
  echo "guarded: $1" >&2; exit "$2"
}
while kill -0 "$pid" 2>/dev/null; do
  sleep 5
  now=$(date +%s)
  [ "$now" -ge "$deadline" ] && stop "time limit (${hours} h) reached" 124
  if [ "$now" -ge "$next_check" ]; then
    "$here/stop_check.sh" >/dev/null && stop "stop switch is on" 99
    next_check=$(( now + 600 ))
  fi
done
wait "$pid"
