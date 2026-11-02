#!/bin/bash
cd /home/user/degree-diameter/research/squads/raise_d8b/r1/c16
nice -n 10 ./lift2 1 8 47 8 70 11 out2_m1_p47.sol 2>/dev/null
nice -n 10 ./lift2 2 4 37 8 70 11 out2_m2_p37.sol 2>/dev/null
echo DONE
