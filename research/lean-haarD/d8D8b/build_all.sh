#!/usr/bin/env bash
# Serial build of the Delta8*D8 record (239,904): one `lake build` per module, stopping at the first failure.
# Parallel builds run out of memory (one stage peaks near 6 GB). Logs go to $LOG (default: the scratchpad).
set -u
ROOT="$(git -C "$(dirname "$0")" rev-parse --show-toplevel)"
export PATH="$HOME/.elan/bin:$PATH"
LOG="${LOG:-$ROOT/../scratch-d8D8b-build.log}"
cd "$ROOT/lean" || exit 1
mods=()
for k in $(seq 0 48); do
  for t in AA AB BB; do mods+=("BipartiteDD.Haar.D8D8b.Cert$t$k"); done
done
mods+=("BipartiteDD.Haar.D8D8b.Cover" "BipartiteDD.Haar.D8D8b.Covers" "BipartiteDD.Haar.D8D8b.Record")
for m in "${mods[@]}"; do
  if bash "$ROOT/scripts/stop_check.sh" >/dev/null; then echo "STOP requested" >> "$LOG"; exit 2; fi
  start=$(date +%s)
  if timeout 3000 lake build "$m" > "$LOG.tmp" 2>&1; then
    echo "OK $m $(( $(date +%s) - start ))s" >> "$LOG"
  else
    echo "FAIL $m" >> "$LOG"; cat "$LOG.tmp" >> "$LOG"; exit 1
  fi
done
echo "ALL MODULES BUILT" >> "$LOG"
