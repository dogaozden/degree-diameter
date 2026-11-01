#!/bin/bash
# refine the 6+6 / meta 13 32 5 near miss (cost 97) and compare the other 6+6 groups (60 s each unless noted)
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
r=$(nice -n 10 ./hgw rb12.txt g66/meta_13_32_5.bin 240 21 1 r3_m13_refine r12m13_init.sol 2>/dev/null); echo "refine m13 240s $r" >> run3.log
r=$(nice -n 10 ./hgw rb12.txt g66/meta_19_22_18.bin 60 22 1 r3_m19 2>/dev/null); echo "rb12 meta_19_22_18 $r" >> run3.log
r=$(nice -n 10 ./hgw rb12.txt g66/meta_7_60_3.bin 60 23 1 r3_m7 2>/dev/null); echo "rb12 meta_7_60_3 $r" >> run3.log
echo DONE3 >> run3.log
