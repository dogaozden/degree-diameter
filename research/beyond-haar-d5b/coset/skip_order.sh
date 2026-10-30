#!/bin/bash
# usage: skip_order.sh ORDER H  -- stop the running sweep_exh.sh of that order (its queue continues with the next order)
cd "$(dirname "$0")"
for p in $(pgrep -f "[s]weep_exh.sh $1 $2 "); do pkill -P $p; kill $p; done
sleep 1
rm -rf tmpx_$1_$2_*
echo "$(date -u +%H:%M) skipped the rest of order $1 (|H| = $2): many class pairs, costs far from 0" >> logs/skipped.log
