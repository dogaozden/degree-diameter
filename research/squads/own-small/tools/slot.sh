#!/bin/bash
# slot.sh SECONDS CMD...: run CMD on one of NSLOTS CPU slots (default 3), waiting for a free slot; nice 10, timeout SECONDS.
# Every squad run longer than ~20 s must go through this gate so that each run gets a whole core.
NS=${NSLOTS:-4}; LD=/tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/slots
mkdir -p $LD; secs=$1; shift
while true; do
  for i in $(seq 0 $((NS-1))); do
    exec {fd}>$LD/slot$i
    if flock -n $fd; then
      echo "[slot $i] $(date -u +%H:%M:%S) start: $*" >> $LD/log
      timeout $secs nice -n 10 "$@"; rc=$?
      echo "[slot $i] $(date -u +%H:%M:%S) end rc=$rc: $1" >> $LD/log
      flock -u $fd; exec {fd}>&-; exit $rc
    fi
    exec {fd}>&-
  done
  sleep 3
done
