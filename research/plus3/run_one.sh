#!/bin/sh
# run_one.sh SECONDS ARGS... : one sat_ext.py job with an external time limit; prints UNKNOWN on timeout.
T="$1"; shift
cd "$(dirname "$0")"
out=$(timeout "$T" nice -n 15 python3 sat_ext.py "$@" --time 100000 --save 2>/dev/null)
rc=$?
if [ $rc -eq 124 ]; then echo "args: $* UNKNOWN (external timeout ${T}s)"; else echo "$out" | grep -v "^ *$"; fi
