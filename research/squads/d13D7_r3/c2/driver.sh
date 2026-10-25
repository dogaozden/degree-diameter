#!/bin/bash
# card c2 (squad r3): sequential LNS runs from the 364 orbit-union seed; each run <= 600 s CPU (clock()), timeout 900 s.
cd /home/user/degree-diameter/research/squads/d13D7_r3/c2
HEX=/home/user/degree-diameter/research/d13D7/hex/hex_q11.bin
SEED=/home/user/degree-diameter/research/squads/d13D7_r3/c2/seed364_idx.txt
export OMP_NUM_THREADS=1
# args after OUT: CPU_SECONDS SEED MODE CMAX JMAX GMAX PFIBER NODELIMIT KSTALL KCMAX RESTORE PPLAT GMODE
run() { name=$1; shift; timeout 900 nice -n 10 ./lns $HEX $SEED run_$name.idx "$@" > run_$name.out 2> run_$name.err; echo "$name exit $? $(date +%T)" >> driver.log; }
run ctrl 180 1 0 3 40 6 0 200000 0 2 0 0.5 0
run k1 600 31 0 3 40 6 0 200000 5 1 0 0.5 1
run k2 600 32 0 5 60 10 0 200000 10 3 1 0.5 1
run k3 600 33 0 2 30 4 0 200000 10 2 0 0.5 0
echo ALLDONE >> driver.log
