#!/bin/bash
# ILS on the (4,5) record graph (162 vertices) over non-abelian groups of order 32..40 (60 CPU-s each)
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
for g in g45/dih_17.bin g45/dih_18.bin g45/dih_19.bin g45/meta_13_3_3.bin g45/meta_9_4_8.bin g45/dih_16.bin g45/meta_5_8_2.bin g45/agl1_5_x_cyc_2.bin; do
  r=$(nice -n 10 ./hgw d4d5.txt $g 60 7 1 o45_$(basename $g .bin) 2>/dev/null)
  echo "$g $r" >> run45.log
done
echo DONE45 >> run45.log
