#!/bin/bash
# 6+6 (b=12, random 4-regular bipartite) and 7+7 (b=14) bases over non-abelian groups of order 356..420, 60 CPU-s each
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONEPG runpg.log 2>/dev/null; do sleep 5; done
for g in g66/meta_13_32_5.bin g66/meta_19_22_18.bin g66/meta_7_60_3.bin; do
  r=$(nice -n 10 ./hgw rb12.txt $g 60 9 1 o66_$(basename $g .bin) 2>/dev/null); echo "rb12 $g $r" >> run66.log
done
for g in g66/meta_7_51_2.bin g66/meta_9_40_8.bin; do
  r=$(nice -n 10 ./hgw rb14.txt $g 60 9 1 o66_$(basename $g .bin) 2>/dev/null); echo "rb14 $g $r" >> run66.log
done
echo DONE66 >> run66.log
