#!/bin/bash
# q2.sh: sequential director checks (job beyond-d13): (7,13) e10, (8,13) director, then (8,14) once the (9,13) check is done
cd "$(dirname "$0")"; export CTH=${CTH:-1}
for f in runs/d7D13_sl_229_13_orb3-2-1_e10.out runs/d8D13_sl_499_7_orb3-2-2_s2.out; do echo "$(date -u +%T) check $f"; ./gen.sh $f; done
while pgrep -f 'haarcheck_gen runs/d9D13' > /dev/null; do sleep 30; done
for f in runs/d8D14_psl_409_157_orb3-2-2_s2.out; do echo "$(date -u +%T) check $f"; CTH=2 ./gen.sh $f; done
echo "Q2 DONE $(date -u +%T)"
