#!/bin/bash
# second batch: wait for the first batch, then two lanes (at most 2 heavy runs at once)
cd /home/user/degree-diameter/research/squads/c157b-r1/c4
HEX=/home/user/degree-diameter/research/squads/c157b-r1/shared/hex_q11.bin
while [ ! -f done.flag ]; do sleep 3; done
run() { name=$1; secs=$2; shift 2; timeout 1200 nice -n 10 ./orbmis $HEX $secs 7 out_$name.txt "$@" > log_$name.txt 2>&1; }
( run MONO600 60 perm_mono_d1.txt perm_mono_d2.txt perm_mono_P3.txt perm_mono_T2.txt; run SIGT200 60 perm_sigma.txt perm_d1.txt perm_d2.txt ) &
( run N240 60 perm_g120.txt perm_h240.txt; run SIGG120 60 perm_sigma.txt perm_g120.txt ) &
wait
echo ALLDONE2 > done2.flag
