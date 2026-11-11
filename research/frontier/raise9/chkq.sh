#!/bin/bash
# chkq.sh TAG...: wait until no haarcheck_gen check is running, then chk.sh TAG... (one check at a time)
cd "$(dirname "$0")"
while pgrep -x haarcheck_gen >/dev/null; do sleep 15; done
./chk.sh "$@"
