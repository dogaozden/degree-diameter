#!/bin/bash
# chk.sh TAG...: haarcheck_gen (independent low-memory checker, BFS from (e,A) and (e,B)) on runs/TAG.out, CTH threads
# (default 2); log in checks/TAG.gen.txt (start/end, sha256, exit code); VALID files are copied to sols/TAG.txt.
cd "$(dirname "$0")"; mkdir -p checks sols
for tag in "$@"; do
  f=runs/$tag.out; out=checks/$tag.gen.txt
  { echo "checker: haarcheck_gen (research/frontier/haarcheck_gen.c)"; echo "file: $f"; echo "sha256 $(sha256sum $f)"
    echo "start: $(date -u +%FT%TZ)"; t0=$(date +%s)
    OMP_NUM_THREADS=${CTH:-2} ../beyond11/bin/haarcheck_gen $f; rc=$?
    echo "exit: $rc"; echo "end: $(date -u +%FT%TZ) ($(( $(date +%s) - t0 )) s)"; } > $out 2>&1
  v=$(grep -hE "^VALID|^INVALID" $out | tail -1); echo "$(date -u +%T) $tag: $v"
  grep -q "^VALID" $out && cp $f sols/$tag.txt
done
