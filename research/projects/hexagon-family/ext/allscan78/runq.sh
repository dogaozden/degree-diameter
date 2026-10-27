#!/bin/bash
# many seeds of ext_all.py: $1 = q, $2 = R file, $3 = spread file, $4 = bar (keep only sets above it), $5 $6 seed range
cd /home/user/degree-diameter/research/projects/hexagon-family/ext
q=$1; R=$2; SP=$3; bar=$4
for s in $(seq $5 $6); do
  for o in rand ovl nx; do
    timeout 300 nice -n 19 python3 ext_all.py $q $R $SP allscan78/q${q}${o}_s$s $s $o 100 250 2>&1 | grep RESULT >> allscan78/q${q}m.log
    k=$(tail -1 allscan78/q${q}m.log | grep -o "= [0-9]*;" | grep -o "[0-9]*")
    [ -n "$k" ] && [ "$k" -le $bar ] && rm -f allscan78/q${q}${o}_s$s.pairs
  done
done
echo DONE >> allscan78/q${q}m.log
