#!/bin/bash
# usage: run_pov.sh CORE SEED SECS NAME   (c1 driver: pov2 from a T3 core, then scored with setcheck)
cd /home/user/degree-diameter/research/squads/d10D7-r6/c1 || exit 1
mkdir -p finals logs
H=/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin
timeout 1700 nice -n 10 ./pov2 $H $2 $3 finals/$4.txt 7 10 200000 5 1000000000000 0 $1 > logs/$4.out 2> logs/$4.err
echo "pov2 exit $?"
echo "core $(wc -l < $1) pts"
/home/user/degree-diameter/research/squads/d10D7-r4/tools/setcheck $H finals/$4.txt points opposite
