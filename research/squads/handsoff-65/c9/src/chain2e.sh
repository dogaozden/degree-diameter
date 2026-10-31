#!/bin/sh
# after the running longrun.py: tabu (exact-ish single-voltage moves) from the best 2+2 vl solutions, then the 3+3 scan
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
while pgrep -f "longrun.py" >/dev/null; do sleep 10; done
INIT=sol SECS=300 SEED=1 timeout 600 nice -n 10 ../shared/tabu runs/F_L15_174_4.base groups/sg_174_4.txt runs/tabu_174_4_s1.sol > runs/tabu_174_4_s1.out 2> runs/tabu_174_4_s1.err
INIT=sol SECS=300 SEED=2 timeout 600 nice -n 10 ../shared/tabu runs/F_L15_174_1.base groups/sg_174_1.txt runs/tabu_174_1_s2.sol > runs/tabu_174_1_s2.out 2> runs/tabu_174_1_s2.err
python3 -I src/scan_vl.py E_L14 base_L14.base 115,116,117,118,119,120 12 60000 1
