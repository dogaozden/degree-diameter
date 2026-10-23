#!/usr/bin/env bash
# Builds the Delta9*D8 (PSL(2,19) x Z79) stage modules FROM..TO (inclusive), one at a time, in the foreground.
# Usage: bash research/lean-haarD/d9D8c/build_stages.sh FROM TO   (stage numbers, e.g. 1 4)
# Each module's log goes to /tmp is avoided: logs go to research/lean-haarD/d9D8c/logs/. Stops at the first failure.
set -u
from=$1; to=$2
root=$(cd "$(dirname "$0")/../../.." && pwd)
logdir="$root/research/lean-haarD/d9D8c/logs"; mkdir -p "$logdir"
export PATH=$HOME/.elan/bin:$PATH
cd "$root/lean" || exit 1
for k in $(seq "$from" "$to"); do
  m=$(printf "BipartiteDD.Haar.D9D8c.Stage%02d" "$k")
  s=$(date +%s)
  timeout 580 lake build "$m" > "$logdir/$m.log" 2>&1
  rc=$?
  echo "$(date -u +%T) $m rc=$rc secs=$(( $(date +%s) - s ))"
  if [ "$rc" -ne 0 ]; then echo "FAILED $m (rc=$rc)"; exit "$rc"; fi
done
echo "BATCH OK $from..$to"
