#!/bin/bash
# final batch: longer runs for the two groups with the best ILS values; starts after batch 2
cd /home/user/degree-diameter/research/squads/c157b-r1/c4
HEX=/home/user/degree-diameter/research/squads/c157b-r1/shared/hex_q11.bin
while [ ! -f done2.flag ]; do sleep 3; done
( timeout 1200 nice -n 10 ./orbmis $HEX 150 11 out_N240L.txt perm_g120.txt perm_h240.txt > log_N240L.txt 2>&1 ) &
( timeout 1200 nice -n 10 ./orbmis $HEX 150 11 out_T100L.txt perm_d1.txt perm_d2.txt > log_T100L.txt 2>&1 ) &
wait
echo ALLDONE3 > done3.flag
