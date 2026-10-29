#!/bin/bash
# usage: exh/queue_b4a2x.sh SECS "o_i o_i ..."   run b4a2x on each SmallGroup(o,i), at most 4 at a time, SECS each
# (a run that hits the time limit is recorded as partial: its .sol file holds what it found).
TL=$1
for gi in $2; do
  while [ $(pgrep -c -f "^[.]/exh/b4a2x ") -ge 4 ]; do sleep 5; done
  o=${gi%_*}; i=${gi#*_}
  ( r=$(timeout $TL ./exh/b4a2x exh/grp/g${o}_$i.txt exh/grp/g${o}_$i.aut 2>&1 > exh/runs/b4a2x_${o}_$i.sol | tail -1)
    [ -z "$r" ] || [ "${r#closed}" != "$r" ] && r="partial: stopped after $TL s, $(wc -l < exh/runs/b4a2x_${o}_$i.sol) solutions so far"
    echo "$o $i :: $r" >> exh/runs/b4a2x_$o.txt ) &
  sleep 1
done
wait
echo QUEUE_DONE >> exh/runs/queue.log
