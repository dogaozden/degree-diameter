#!/bin/bash
# refine the 6+6 / meta 7 60 3 candidate (cost 91 at 60 s), after run4
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE4 run4.log 2>/dev/null; do sleep 5; done
r=$(nice -n 10 ./hgw rb12.txt g66/meta_7_60_3.bin 360 41 1 r5_m7 r12m7_91.sol 2>/dev/null); echo "refine m7_60_3 360s $r" >> run5.log
echo DONE5 >> run5.log
