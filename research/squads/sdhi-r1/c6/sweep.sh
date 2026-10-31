#!/bin/bash
# c6 sweep: inv + e (ORBIT 2 3 1) on order 47,881-49,000 groups, plus plain orbit comparison on psl 19 14
B=/home/user/degree-diameter/research/selfdual-hi/src/haar_sd
cd /home/user/degree-diameter/research/squads/sdhi-r1/c6

run() { tag=$1; shift; env THREADS=1 "$@" 2>&1 | tail -n 3 > "$tag.log"; }
ORBIT="2 3 1" SDUAL="inv 1 0" timeout 120 nice -n 10 $B 7 8 40 21 8 sw_psl5_800.sol psl 5 800 > sw_psl5_800.log 2>&1
ORBIT="2 3 1" SDUAL="inv 1 0" timeout 120 nice -n 10 $B 7 8 40 21 8 sw_psl13_44.sol psl 13 44 > sw_psl13_44.log 2>&1
ORBIT="2 3 1" SDUAL="inv 1 0" timeout 120 nice -n 10 $B 7 8 40 21 8 sw_psl11_73.sol psl 11 73 > sw_psl11_73.log 2>&1
ORBIT="2 3 1" SDUAL="inv 1 0" timeout 120 nice -n 10 $B 7 8 40 21 8 sw_psl7_288.sol psl 7 288 > sw_psl7_288.log 2>&1
ORBIT="2 3 1" timeout 120 nice -n 10 $B 7 8 40 21 8 plain_psl19_14.sol psl 19 14 > plain_psl19_14.log 2>&1
echo done > sweep.done
