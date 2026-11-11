#!/bin/bash
# sweep.sh LIST LOG: exh4 on every "N m k r" line of LIST (d = 4, D = 10); one EXH4 line per group appended to LOG
cd "$(dirname "$0")"
while read N m k r rest; do
  [ -z "$m" ] && continue
  grep -q "group=meta $m $k $r " "$2" 2>/dev/null && continue
  ./exh4 4 10 $m $k $r 5 >> "$2" 2> err/m${m}_k${k}_r${r}.err
done < "$1"
echo "SWEEP DONE $(date -u +%T)" >> "$2"
