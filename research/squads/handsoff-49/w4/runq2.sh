#!/bin/bash
# prioritised queue (replaces the earlier PG and 6+6 queues): waits for run45 to finish
cd /home/user/degree-diameter/research/squads/handsoff-49/w4
while ! grep -q DONE45 run45.log 2>/dev/null; do sleep 5; done
r=$(nice -n 10 ./hgw d4d5.txt g45/dih_16.bin 240 11 1 o45_dih16_long 2>/dev/null); echo "d4D5 dih16 240s $r" >> runq2.log
for g in gpg/sl2_3_x_cyc_8.bin gpg/meta_14_14_13.bin gpg/heis_3_x_cyc_8.bin gpg/agl1_7_x_cyc_5.bin; do
  r=$(nice -n 10 ./hgw pg23.txt $g 60 9 1 opg_$(basename $g .bin) 2>/dev/null); echo "PG $g $r" >> runq2.log
done
r=$(nice -n 10 ./hgw rb12.txt g66/meta_13_32_5.bin 60 9 1 o66_meta_13_32_5 2>/dev/null); echo "rb12 meta_13_32_5 $r" >> runq2.log
r=$(nice -n 10 ./hgw rb14.txt g66/meta_7_51_2.bin 60 9 1 o66_meta_7_51_2 2>/dev/null); echo "rb14 meta_7_51_2 $r" >> runq2.log
echo DONEQ2 >> runq2.log
