#!/bin/bash
# q3.sh: after the (8,13) check, check the r3/f13 (7,14) find (job beyond-d13)
cd "$(dirname "$0")"; export CTH=1
while pgrep -f 'haarcheck_gen runs/d8D13' > /dev/null; do sleep 15; done
for f in runs/d7D14_sl_163_193_orb3-2-1_f13.out; do echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q3 DONE $(date -u +%T)"
