#!/bin/bash
cd /home/user/degree-diameter/research/squads/d10D7-r5/c5
for s in 11 12 13 14 15 16; do
  timeout 400 nice -n 10 ./mis8 /home/user/degree-diameter/research/d10D7/hex/hex_q8.bin ell_cand_ids.txt 100 145 1000000 $s out/ellB$s > out/ellB$s.log 2>&1
done
echo done > out/ell_done.flag
