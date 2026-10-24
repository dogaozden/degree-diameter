#!/bin/bash
# scan m for X(M)-type lifts with constant hop voltages 1..k, report uncovered at maxlen 7
q=$1; k=$2; shift 2
for m in "$@"; do
  python3 mk_xm.py $q $k $m 1 /tmp/sc_$q_$k_$m.base > /dev/null
  r=$(./liftcheck /tmp/sc_$q_$k_$m.base 7 2>/dev/null | head -1)
  echo "q=$q k=$k m=$m : $r"
done
