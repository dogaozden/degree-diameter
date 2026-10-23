#!/bin/bash
# save_sol.sh QUEUE_OUTDIR TAG...: copy a VALID orbq solution (+ its log) into ../frontier/sols and runs/, commit, push.
OUT=$1; shift
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
for tag in "$@"; do
  grep -q "^VALID" "$OUT/$tag.log" || { echo "$tag: no VALID line, skipped"; continue; }
  cp "$OUT/$tag.txt" "$REPO/research/frontier/sols/" && cp "$OUT/$tag.log" "$REPO/research/structured/runs/"
  echo "$tag: $(grep '^VALID' "$OUT/$tag.log")"
done
cd "$REPO" && git add research/frontier/sols research/structured && git commit -q -m "structured: $(for t in "$@"; do grep -h '^VALID' "$OUT/$t.log" | head -1 | grep -o 'd=[0-9]* D=[0-9]* group=.* vertices=[0-9]*'; done | tr '\n' ';') $(grep -ho "orbit k=[0-9]* m=[0-9]* f=[0-9]*" "$OUT/$1.log" | head -1 | sed "s/orbit //") orbit search [haar_sym full check + $(grep -q 'eccA=' "$OUT/$1.log" && echo 'haarcheck_sl + haarcheck2' || (grep -q 'group=psl' "$OUT/$1.log" && grep -q 'distinct generators' "$OUT/$1.log" && echo haarcheck_psl || echo build_haar2)) VALID]

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Ayob3KjJs51WGU95fnUsyn" && git push -q origin HEAD 2>&1 | tail -1
