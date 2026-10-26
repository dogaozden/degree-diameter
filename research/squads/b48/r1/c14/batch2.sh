#!/bin/bash
cd /home/user/degree-diameter/research/squads/b48/r1/c14
T=/home/user/degree-diameter/research/squads/b48/tools
for g in g1152_sing8 g1200_sing24 g1210_diag21 g1125_ord3 g1188_ord4; do
  THREADS=1 QUIET=1 timeout 120 nice -n 10 $T/lift $T/bases/dipole4.txt $g.bin 4 8 30 1 8 sol_$g.sol > run_$g.log 2>&1
done
echo DONE > batch2.done
