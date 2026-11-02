#!/bin/bash
# usage: evalall.sh listfile ; prints cost, N, path for each state file (group read from header)
while read f; do
  [ -f "$f" ] || continue
  read d D mt m k r n1 x N rest < <(head -1 "$f")
  out=$(timeout 60 nice -n 10 env THREADS=1 EVAL="$f" ./hmeta $d $D 1 1 1 /dev/null $m $k $r 2>&1 | tail -1)
  echo "$out | $f | m=$m k=$k r=$r"
done < "$1"
