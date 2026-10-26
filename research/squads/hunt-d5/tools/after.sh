#!/bin/bash
# after.sh PIDFILE_OR_PIDS -- CMD...: wait until the given pids are gone, then run CMD (hunt-d5 job chaining)
pids=(); while [ "$1" != "--" ]; do pids+=($1); shift; done; shift
for p in "${pids[@]}"; do while kill -0 $p 2>/dev/null; do sleep 5; done; done
exec "$@"
