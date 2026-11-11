#!/bin/bash
cd /home/user/degree-diameter/research/squads/raise_d8b/r1/c16
for args in "1 8 41" "1 8 43" "2 4 31" "2 4 37"; do
  set -- $args
  nice -n 10 ./lift2 $1 $2 $3 8 40 7 out_m$1_p$3.sol 2>/dev/null
done
echo DONE
