#!/bin/bash
# calibration ladder: sdhi tabu, K=7, D=6, every psi option and type, SECS per psi/type
cd "$(dirname "$0")/.."
run() { out=logs/calib/$1.txt; shift; SECS=${SECS:-15} MAXSOL=2 timeout 3000 nice -n 5 src/sdhi 7 6 "$@" > $out 2>&1; }
run psl7_9 psl 7 cyc 9 &
run psl7_11 psl 7 cyc 11 &
run psl11_3 psl 11 cyc 3 &
run psl13_2 psl 13 cyc 2 &
wait
run psl7_13 psl 7 cyc 13 &
run pgl7_7 pgl 7 cyc 7 &
run sl7_7 sl 7 cyc 7 &
run psl11_4 psl 11 cyc 4 &
wait
