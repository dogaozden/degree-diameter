#!/bin/bash
# usage: save.sh SOL NAME   -> independent check (haarcheck_gen, BFS from both sides); if VALID, copy SOL to
# research/frontier/sols/NAME.txt and the check output to research/frontier/beyond/checks/NAME.gen.txt
set -e
here=$(cd "$(dirname "$0")" && pwd); sol=$1; name=$2
out=$here/../beyond/checks/$name.gen.txt
{ echo "# $name: haarcheck_gen (research/frontier/haarcheck_gen.c) on $(sha256sum "$sol" | cut -c1-16)..., $(date -u)"; OMP_NUM_THREADS=${T:-2} "$here/bin/haarcheck_gen" "$sol"; } > "$out.tmp" 2>&1 || true
if grep -q "^VALID" "$out.tmp"; then mv "$out.tmp" "$out"; cp "$sol" "$here/../sols/$name.txt"; echo "SAVED $name: $(grep ^VALID "$out" | cut -c1-120)"; else echo "NOT VALID $name"; tail -n 2 "$out.tmp"; rm -f "$out.tmp"; fi
