#!/bin/bash
# w6: Haar graphs of the other groups of order 2485 (cost 0 = a second valid 4,970 base for surgery).
H=/home/user/degree-diameter/research/squads/handsoff-49
cd $H/w6
while pgrep -f "surgsa2 " > /dev/null; do sleep 2; done
for g in g_m71_5_x7 g_m71_7_x5 g_cyc2485; do
  for seed in 1 2; do
    timeout 200 nice -n 10 $H/tools/haar_tab 4 9 40 $seed 8 groups/sol_${g}_$seed.txt tab groups/$g.bin 1 > groups/log_${g}_$seed.txt 2>&1
    tail -1 groups/log_${g}_$seed.txt >> groups/summary.txt
    echo "$g seed $seed: $(tail -1 groups/log_${g}_$seed.txt)" >> groups/summary.txt
  done
done
echo DONE >> groups/summary.txt
