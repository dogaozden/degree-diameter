#!/bin/bash
# save_sol.sh QUEUE_OUTDIR TAG...: copy a VALID orbq solution (+ its log) into ../frontier/sols and runs/, commit, push.
OUT=$1; shift
REPO=$(cd "$(dirname "$0")/../../.." && pwd)
for tag in "$@"; do
  grep -q "^VALID" "$OUT/$tag.log" || { echo "$tag: no VALID line, skipped"; continue; }
  fam=$(head -1 "$OUT/$tag.txt" | awk '{print $3}'); NN=$(head -1 "$OUT/$tag.txt" | awk '{print $NF}')
  if [ "$fam" = sl ] && [ "$NN" -gt 10000000 ] && ! grep -q "eccA=" "$OUT/$tag.log"; then
    echo "$tag: haarcheck2 verdict not in the log yet, skipped"; continue; fi
  cp "$OUT/$tag.txt" "$REPO/research/frontier/sols/" && cp "$OUT/$tag.log" "$REPO/research/structured/runs/"
  echo "$tag: $(grep '^VALID' "$OUT/$tag.log")"
done
checkers() {   # which checkers left a VALID verdict in the log (each has its own line format)
  c=()
  grep -qE '^VALID d=[0-9]+ D=[0-9]+ group=.* vertices=[0-9]+$' "$1" && c+=(build_haar2)
  grep -qE '^VALID d=.* group=sl .*distinct generators' "$1" && c+=(haarcheck_sl)
  grep -qE '^VALID d=.* group=psl .*distinct generators' "$1" && c+=(haarcheck_psl)
  grep -qE '^VALID d=[0-9]+ D=[0-9]+ vertices=[0-9]+ eccA=' "$1" && c+=(haarcheck2)
  grep -qE '^RESULT VALID d=' "$1" && c+=(check_haar_indep)
  local IFS=+; echo "${c[*]}" | sed 's/+/ + /g'
}
cd "$REPO" && git add research/frontier/sols research/structured && git commit -q -m "structured: $(for t in "$@"; do grep -h '^VALID' "$OUT/$t.log" | head -1 | grep -o 'd=[0-9]* D=[0-9]* group=.* vertices=[0-9]*'; done | tr '\n' ';') $(grep -ho "orbit k=[0-9]* m=[0-9]* f=[0-9]*" "$OUT/$1.log" | head -1 | sed "s/orbit //") orbit search [haar_sym full check + $(checkers "$OUT/$1.log") VALID]

Co-Authored-By: Claude Opus 5.5 <noreply@anthropic.com>
Claude-Session: https://claude.ai/code/session_01Ayob3KjJs51WGU95fnUsyn" && git push -q origin HEAD 2>&1 | tail -1
