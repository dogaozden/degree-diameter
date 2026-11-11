#!/bin/bash
# screen exact-order Frobenius-type groups at (5,9), 50 s each, THREADS=1
cd /home/user/degree-diameter/research/squads/beyond13/r7/j02
for g in "14895 993 15 4" "15015 1001 15 9" "15025 601 25 2" "15167 523 29 9" "15223 1171 13 86" "15279 463 33 36" "15309 567 27 4" "15315 1021 15 67" "15327 1179 13 244" "15345 1023 15 25" "15351 731 21 52" "15379 1183 13 92" "15399 531 29 19" "15405 395 39 11" "15405 1185 13 46" "15435 735 21 16" "15477 469 33 4"; do
  set -- $g
  out=scr_$2_$3_$4
  res=$(env T0=8 T1=1 REHEAT=400 THREADS=1 timeout 70 nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/meta/hmeta 5 9 50 7 8 $out $2 $3 $4 2>/dev/null | grep RESULT)
  echo "$1 m=$2 k=$3 r=$4 :: $res" >> screen.log
  case "$res" in *best=0\ *) echo FOUND $out >> screen.log; break;; esac
done
echo DONE >> screen.log
