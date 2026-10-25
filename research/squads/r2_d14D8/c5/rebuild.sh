#!/bin/bash
# rebuild.sh BESTM : reproduce the best q=7 design of this folder (BESTM = 17: run3_m17.txt) and check it exactly.
# Chain (deterministic given the seeds; time limits 540/420/300 s are upper bounds):
#   mkq7.py 1                       quotient structure of H(7) under Sigma (|Sigma| = 19), 1032 orbit reps, degree 10
#   symsa7  seed 1 from random      exact m = 15 at 66 s (run1_m15.txt)
#   symsa7b seed 2 from run1_m15    exact m = 16 at 95 s (run2_m16.txt)
#   symsa7b seed 3 from run2_m16    exact m = 17 at 60 s (run3_m17.txt)
# then the exact checker: base graph + lifteval over all 19608 sources (COST 0 means diameter <= 8).
set -e
D=/home/user/degree-diameter/research/squads/r2_d14D8/c5
cd "$D"
python3 mkq7.py 1
./symsa7 qstruct_1.txt 12 15 540 1 40 run1 - 0.5
./symsa7b qstruct_1.txt 15 31 420 2 40 run2 run1_m15.txt 0.5
./symsa7b qstruct_1.txt 16 31 300 3 40 run3 run2_m16.txt 0.5
./verify.sh "run3_m$1.txt" "$1"
