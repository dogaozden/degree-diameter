#!/bin/bash
# screen: b22_t1, D=9, 8 s per group, seed 1
cd /home/user/degree-diameter/research/squads/b48/r3/d10
for G in "1255 251 5 20" "1263 421 3 20" "1299 433 3 198" "1317 439 3 171" "1355 271 5 10" "1371 457 3 133" "1379 197 7 36" "1389 463 3 21" "1281 427 3 74" "1252 313 4 25" "1310 131 10 42" "1314 73 18 18" "1250 125 10 24" "1260 315 4 62" "1338 223 6 40"; do
  set -- $G
  echo "== N=$1 meta:$2:$3:$4"
  QUIET=1 THREADS=1 timeout 120 nice -n 10 /home/user/degree-diameter/research/squads/b48/tools/flift /home/user/degree-diameter/research/squads/b48/tools/bases/b22_t1.txt meta:$2:$3:$4 4 9 8 1 8 screen/t1_$2_$3_$4.txt 2>&1 | grep RESULT
done
