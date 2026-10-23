#!/bin/bash
# save_sol.sh QUEUE_OUTDIR TAG...: copy a VALID orbq solution (+ its log) into ../frontier/sols and runs/, commit, push.
OUT=$1; shift
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
for tag in "$@"; do
  grep -q "^VALID" "$OUT/$tag.log" || { echo "$tag: no VALID line, skipped"; continue; }
  cp "$OUT/$tag.txt" "$REPO/research/frontier/sols/" && cp "$OUT/$tag.log" "$REPO/research/structured/runs/"
  echo "$tag: $(grep '^VALID' "$OUT/$tag.log")"
done
cd "$REPO" && git add research/frontier/sols research/structured && git commit -q -m "structured: $(for t in "$@"; do grep -h '^VALID' "$OUT/$t.log" | awk '{print $2, $3, $NF}'; done | tr '\n' ';') k=3 orbit search [haar_sym full check + build_haar2 VALID]

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01QKEyevacJ1J3hTieaJQKkq" && git push -q 2>&1 | tail -1
