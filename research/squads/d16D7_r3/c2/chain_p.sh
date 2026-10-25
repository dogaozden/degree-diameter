#!/bin/bash
# expand the best quotient solutions (exact light fill), score them, then polish each with the original ktabu on the
# full orbit graph (420 s CPU each, through the shared slot runner)
cd /home/user/degree-diameter/research/squads/d16D7_r3/c2
Q=/home/user/degree-diameter/research/squads/d16D7_r3/quot
R2=/home/user/degree-diameter/research/squads/d16D7_r2
S=/home/user/degree-diameter/research/squads/d16D7_r3/run_slot.sh
CE=/home/user/degree-diameter/research/squads/cells/d16D7
python3 $CE/ogquot_expand.py $Q/q9_pts.map q9q_pts.sol.exact exp_pts.txt && python3 $R2/ogscore.py $R2/og_pts.txt exp_pts.txt
python3 $CE/ogquot_expand.py $Q/q9_lines.map q9q_lines.sol.exact exp_lines.txt && python3 $R2/ogscore.py $R2/og_lines.txt exp_lines.txt
$S ./ktabu $R2/og_pts.txt exp_pts.txt polish_pts.sol 420 1 > polish_pts.out 2> polish_pts.log
echo "pts polish rc=$?"
$S ./ktabu $R2/og_lines.txt exp_lines.txt polish_lines.sol 420 1 > polish_lines.out 2> polish_lines.log
echo "lines polish rc=$?"
echo done > chain_p.done
