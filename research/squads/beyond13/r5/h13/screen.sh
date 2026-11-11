#!/bin/bash
# RANDORB screen: args are "fam p n"; prints the summary line
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r5/h13
fam=$1; p=$2; n=$3
ORBIT="3 2 0" RANDORB=12 THREADS=1 timeout 300 nice -n 10 $B/bin/haar_big0 6 14 30 1 8 scr_${fam}_${p}_${n}.out $fam $p $n > scr_${fam}_${p}_${n}.log 2>&1
