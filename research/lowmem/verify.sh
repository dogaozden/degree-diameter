#!/bin/bash
# verify.sh SOLFILE [checker...]: run independent low-memory checkers on a Haar solution file (nice 2, line-buffered).
# SL: haarcheck2 (../frontier/haarcheck2.c) and/or haarcheck_sl (../frontier/haarcheck_sl.c);
# PSL: haarcheck_psl (../structured/tools/haarcheck_psl.c, branch claude/structured-search-orbit-w5dd4f).
# Output: runs/<tag>.<checker>.txt with start/end time and exit code.
f=$1; shift; tag=$(basename "$f" .txt); fam=$(head -1 "$f" | awk '{print $3}')
if [ $# -eq 0 ]; then if [ "$fam" = psl ]; then set -- haarcheck_psl; else set -- haarcheck2; fi; fi
for c in "$@"; do
  out=runs/$tag.$c.txt
  { echo "$c start $(date -u +%FT%TZ) on $f"; s=$(date +%s)
    nice -n 2 stdbuf -oL ./$c "$f"; e=$?
    echo "exit $e after $(( $(date +%s) - s )) s, $(date -u +%FT%TZ)"; } > "$out" 2>&1
done
