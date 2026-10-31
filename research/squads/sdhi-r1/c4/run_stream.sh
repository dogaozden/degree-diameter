#!/bin/bash
# usage: run_stream.sh QUEUE OUT ; runs one sdhi tabu per line (m k r psi), TYPES=1+2+2, SECS=8
Q=$1; OUT=$2; SD=/home/user/degree-diameter/research/selfdual-hi/src/sdhi
: > "$OUT"
while read m k r p; do
  echo "### meta $m $k $r PSI=$p" >> "$OUT"
  PSI=$p TYPES="${TYPES:-1+2+2}" SECS=${SECS:-8} STALL=2000 THREADS=1 timeout 120 nice -n 10 $SD 5 8 meta $m $k $r cyc 1 >> "$OUT" 2>&1
done < "$Q"
echo STREAM_DONE >> "$OUT"
