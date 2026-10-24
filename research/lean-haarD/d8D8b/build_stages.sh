#!/usr/bin/env bash
# Resumable serial build of the Delta8*D8 record (239,904): one `lake build` per module, in dependency order.
# Each call builds stages until BUDGET seconds have passed (default 480), then returns; modules already marked
# OK in LOG are skipped, so repeat the call until it prints ALL MODULES BUILT. Stops at the first failure
# (its output is in LOG.<module>). Parallel builds run out of memory (one stage peaks near 6-7 GB).
# Usage: LOG=<file> BUDGET=480 bash research/lean-haarD/d8D8b/build_stages.sh
set -u
ROOT="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
export PATH="$HOME/.elan/bin:$PATH"
LOG="${LOG:-${TMPDIR:-/tmp}/d8D8b-build.log}"
BUDGET="${BUDGET:-480}"
touch "$LOG"
start=$(date +%s)
cd "$ROOT/lean" || exit 1
mods=("BipartiteDD.Haar.D8D8b.Check")
for k in $(seq 0 48); do
  for t in AA AB BB; do mods+=("BipartiteDD.Haar.D8D8b.Cert$t$k"); done
done
mods+=("BipartiteDD.Haar.D8D8b.Cover" "BipartiteDD.Haar.D8D8b.Covers" "BipartiteDD.Haar.D8D8b.Record" "BipartiteDD.Haar.D8D8b.Axioms")
for m in "${mods[@]}"; do
  if grep -q "^OK $m " "$LOG"; then continue; fi
  if [ $(( $(date +%s) - start )) -ge "$BUDGET" ]; then echo "budget reached; next: $m"; exit 3; fi
  if bash "$ROOT/scripts/stop_check.sh" >/dev/null; then echo "STOP requested" >> "$LOG"; exit 2; fi
  t0=$(date +%s)
  if timeout 1500 lake build "$m" > "$LOG.$m" 2>&1; then
    echo "OK $m $(( $(date +%s) - t0 ))s" >> "$LOG"; rm -f "$LOG.$m"
  else
    echo "FAIL $m" >> "$LOG"; echo "FAILED $m (see $LOG.$m)"; exit 1
  fi
done
echo "ALL MODULES BUILT" >> "$LOG"; echo "ALL MODULES BUILT"
