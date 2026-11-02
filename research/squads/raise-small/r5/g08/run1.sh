#!/bin/bash
# usage: run1.sh N m k r seed
N=$1; m=$2; k=$3; r=$4; s=$5
RS=/home/user/degree-diameter/research/frontier/raise_small
cd /home/user/degree-diameter/research/squads/raise-small/r5/g08
THREADS=1 T0=8 T1=1 REHEAT=400 timeout 100 nice -n 10 $RS/bin/hmeta 4 12 40 $s 16 out_${m}_${k}_${r}_$s $m $k $r > log_${m}_${k}_${r}_$s.txt 2>&1
b=$(grep -o 'best=[0-9]*' log_${m}_${k}_${r}_$s.txt | tail -1 | cut -d= -f2)
echo "$N $m $k $r $s $b" >> results.txt
echo "$N $m $k $r seed $s best=$b"
