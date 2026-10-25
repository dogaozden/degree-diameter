#!/bin/bash
# usage: run_one.sh STARMAX SEED TAG  -> builds b2star solution, edge list, and runs apsp (7 7)
set -e
R=/home/user/degree-diameter/research
C=/home/user/degree-diameter/research/squads/d10D7-r4/c7
cd $C
STARMAX=$1 timeout 300 nice -n 10 ./d7hex_c7 b2star $R/d10D7/hex/hex_q5.bin 1000 $2 $C/b2star_$3.sol 4 100000
timeout 300 nice -n 10 ./d7hex_c7 edges $R/d10D7/hex/hex_q5.bin $C/b2star_$3.sol $C/g_$3.edges
timeout 1500 nice -n 10 $R/d10D7/apsp $C/g_$3.edges 7 7
