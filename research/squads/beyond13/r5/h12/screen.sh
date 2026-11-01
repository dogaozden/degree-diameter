#!/bin/bash
B=/home/user/degree-diameter/research/frontier/beyond13
W=/home/user/degree-diameter/research/squads/beyond13/r5/h12
cd $W
for g in "psl 131 139" "psl 151 91" "psl 157 81" "psl 191 45" "psl 137 122" "psl 139 117" "psl 149 95" "psl 131 140" "psl 173 61" "psl 163 73" "sl 541 1" "sl 283 7" "psl 137 124" "psl 139 119"; do
  set -- $g
  ORBIT="3 2 1" THREADS=1 RANDORB=10 timeout 300 nice -n 10 $B/bin/haar_big0 7 13 100 1 4 $W/scr_$1_$2_$3.txt $1 $2 $3 > $W/scr_$1_$2_$3.log 2>&1
done
echo DONE > $W/screen.done
