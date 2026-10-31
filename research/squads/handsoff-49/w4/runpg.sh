#!/bin/bash
# ILS on PG(2,3) (26 vertices) over non-abelian groups of order 192..216 (60 CPU-s each); waits for run45
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE45 run45.log 2>/dev/null; do sleep 5; done
for g in gpg/sl2_3_x_cyc_8.bin gpg/meta_14_14_13.bin gpg/dih_100.bin gpg/semi_7_4_0_6_1_0.bin gpg/meta_13_16_5.bin gpg/agl1_7_x_cyc_5.bin gpg/heis_3_x_cyc_8.bin gpg/sl2_3_x_cyc_9.bin gpg/meta_7_28_6.bin; do
  r=$(nice -n 10 ./hgw pg23.txt $g 60 9 1 opg_$(basename $g .bin) 2>/dev/null)
  echo "$g $r" >> runpg.log
done
echo DONEPG >> runpg.log
