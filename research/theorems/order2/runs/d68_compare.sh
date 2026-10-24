#!/bin/bash
# (6,8): four order-2 symmetries, 6 seeds each, 150 s per seed (ORDER2.md 5.4)
B=/tmp/claude-0/-home-user-degree-diameter/58e8cabc-b55f-55a3-910c-be10e616a47b/scratchpad/src/haar_order2e
cd /tmp/claude-0/-home-user-degree-diameter/58e8cabc-b55f-55a3-910c-be10e616a47b/scratchpad/runs
mkdir -p d68
for s in 1 2 3 4 5 6; do
  ORBIT="2 3 0" timeout 170 nice -n 5 $B 6 8 150 $s 8 d68/sol_psl11x24_r11_s$s.txt psl 11 24 > d68/psl11x24_r11_s$s.log 2>&1
  ORBIT="2 3 0" AR=23 timeout 170 nice -n 5 $B 6 8 150 $s 8 d68/sol_psl11x24_r23_s$s.txt psl 11 24 > d68/psl11x24_r23_s$s.log 2>&1
  ORBIT="2 3 0" timeout 170 nice -n 5 $B 6 8 150 $s 8 d68/sol_sl25_conj_s$s.txt sl 25 1 > d68/sl25_conj_s$s.log 2>&1
  ORBIT="2 3 0" AFROB=1 timeout 170 nice -n 5 $B 6 8 150 $s 8 d68/sol_sl25_frob_s$s.txt sl 25 1 > d68/sl25_frob_s$s.log 2>&1
done
echo done
