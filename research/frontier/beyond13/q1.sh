#!/bin/bash
# q1.sh: sequential director checks (job beyond-d13): wait for the running (7,14) check, then (8,13), then (8,14)
cd "$(dirname "$0")"; export CTH=${CTH:-1}
while pgrep -f 'haarcheck_gen runs/d7D14' > /dev/null; do sleep 20; done
for f in runs/d8D13_sl_911_1_orb3-2-2_c13.out; do echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q1 DONE $(date -u +%T)"
