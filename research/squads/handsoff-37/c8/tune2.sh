#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
run() { echo "== $*"; nice -n 10 ./lns "$@" 2>/dev/null; }
run 150 7 30 2 1 0.5 2 out/t2a
run 150 7 30 3 0.7 0.5 2 out/t2b
run 150 7 30 3 1.3 0.5 2 out/t2c
run 150 7 30 3 1 0.8 2 out/t2d
run 150 7 30 3 1 0.5 3 out/t2e
run 170 7 120 3 1 0.5 2 out/t2f out/ins170_s1.edges
echo ALLDONE
