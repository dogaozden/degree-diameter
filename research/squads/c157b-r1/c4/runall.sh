#!/bin/bash
# two lanes, at most 2 heavy runs at once; each run: timeout 1200 nice -n 10, 60 s of search
cd /home/user/degree-diameter/research/squads/c157b-r1/c4
HEX=/home/user/degree-diameter/research/squads/c157b-r1/shared/hex_q11.bin
run() { name=$1; secs=$2; shift 2; timeout 1200 nice -n 10 ./orbmis $HEX $secs 7 out_$name.txt "$@" > log_$name.txt 2>&1; }
( run G399 60 perm_g133.txt perm_h399.txt; run C120 60 perm_g120.txt; run C60 60 perm_g120p2.txt; run C24 60 perm_g120p5.txt; run T100 60 perm_d1.txt perm_d2.txt ) &
( run C110 60 perm_m110.txt; run B110 60 perm_u.txt perm_d1.txt; run C40 60 perm_g120p3.txt; run C12 60 perm_g120p10.txt ) &
wait
echo ALLDONE > done.flag
