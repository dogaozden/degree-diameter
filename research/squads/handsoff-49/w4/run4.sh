#!/bin/bash
# keep refining the 6+6 / meta 13 32 5 near miss (cost 80), after run3 completes
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE3 run3.log 2>/dev/null; do sleep 5; done
r=$(nice -n 10 ./hgw rb12.txt g66/meta_13_32_5.bin 480 31 1 r4_m13 r12m13_80.sol 2>/dev/null); echo "refine2 m13 480s $r" >> run4.log
echo DONE4 >> run4.log
