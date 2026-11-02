#!/bin/bash
# usage: check_one.sh LABEL OUTFILE cmd args...   (runs one independent checker, logs start/end times, exit code, sha256)
label=$1; out=$2; shift 2
{ echo "checker: $label"; echo "command: $*"; echo "start: $(date -u +%FT%TZ)"; for a in "$@"; do [ -f "$a" ] && echo "sha256 $(sha256sum "$a")"; done
  t0=$(date +%s); "$@"; rc=$?; t1=$(date +%s); echo "exit: $rc"; echo "end: $(date -u +%FT%TZ) ($((t1 - t0)) s)"; } > "$out" 2>&1
