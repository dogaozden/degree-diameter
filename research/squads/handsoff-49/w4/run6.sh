#!/bin/bash
# final refinement of the order-416 candidate (cost 76), after run5
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE5 run5.log 2>/dev/null; do sleep 5; done
r=$(nice -n 10 ./hgw rb12.txt g66/meta_13_32_5.bin 300 51 1 r6_m13 r12m13_76.sol 2>/dev/null); echo "refine3 m13 300s $r" >> run6.log
echo DONE6 >> run6.log
