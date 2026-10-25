#!/bin/bash
# quotient k-fixed tabu (ktq) on both q9 quotients, one run each, through the shared slot runner (120 s CPU each)
cd /home/user/degree-diameter/research/squads/d16D7_r3/c2
Q=/home/user/degree-diameter/research/squads/d16D7_r3/quot
S=/home/user/degree-diameter/research/squads/d16D7_r3/run_slot.sh
$S ./ktq $Q/q9_pts.txt - q9q_pts.sol 120 1 3000000 1000000 > q9q_pts.out 2> q9q_pts.log
$S ./ktq $Q/q9_lines.txt - q9q_lines.sol 120 1 3000000 1000000 > q9q_lines.out 2> q9q_lines.log
echo done > chain_q.done
