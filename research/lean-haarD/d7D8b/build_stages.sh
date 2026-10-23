#!/usr/bin/env bash
# Builds the Delta7*D8 (Z14) modules one at a time, in dependency order, under scripts/guarded.sh.
# Usage: bash research/lean-haarD/d7D8b/build_stages.sh LOGDIR   (run from the lean/ directory's parent = repo root)
# Stops at the first failing module and leaves its log in LOGDIR/<module>.log.
set -u
logdir=$1; mkdir -p "$logdir"
root=$(cd "$(dirname "$0")/../../.." && pwd)
export PATH=$HOME/.elan/bin:$PATH
cd "$root/lean" || exit 1
mods="BipartiteDD.Haar.D7D8.PSL19 BipartiteDD.Haar.Main BipartiteDD.Haar.D7D8.Diam8 BipartiteDD.Haar.D7D8b.Check"
for k in 0 1 2 3 4 5 6 7 8 9; do
  for n in AA AB BB; do mods="$mods BipartiteDD.Haar.D7D8b.Cert$n$k"; done
done
mods="$mods BipartiteDD.Haar.D7D8b.Cover BipartiteDD.Haar.D7D8b.Covers BipartiteDD.Haar.D7D8b.Record BipartiteDD.Haar.D7D8b.Axioms"
for m in $mods; do
  echo "$(date -u +%H:%M:%S) start $m"
  "$root/scripts/guarded.sh" 3 lake build "$m" > "$logdir/$m.log" 2>&1
  rc=$?
  echo "$(date -u +%H:%M:%S) end $m rc=$rc"
  if [ "$rc" -ne 0 ]; then echo "FAILED $m (rc=$rc)"; exit "$rc"; fi
done
echo "ALL OK"
