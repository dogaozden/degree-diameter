#!/bin/sh
# k09: non-bipartite cubic bases lifted with all-odd voltages (chi(a,j) = j mod 2), cell (3,9)
K=/home/user/degree-diameter/research/squads/b48/r5/k09; T=/home/user/degree-diameter/research/squads/b48/tools
cd $K
THREADS=1 NOTREE=1 ODDSTRIDE=16 QUIET=1 timeout 120 nice -n 10 $T/lift $K/k4.txt meta:16:8:7 3 9 40 1 8 $K/k4_m16_8_7.sol
THREADS=1 NOTREE=1 ODDSTRIDE=8 QUIET=1 timeout 120 nice -n 10 $T/lift $K/mob8.txt meta:8:8:3 3 9 40 1 8 $K/mob8_m8_8_3.sol
THREADS=1 NOTREE=1 ODDSTRIDE=13 QUIET=1 timeout 120 nice -n 10 $T/lift $K/pet.txt meta:13:4:5 3 9 40 1 8 $K/pet_m13_4_5.sol
THREADS=1 NOTREE=1 ODDSTRIDE=43 QUIET=1 timeout 120 nice -n 10 $T/lift $K/prism3.txt meta:43:2:42 3 9 40 1 8 $K/prism_d43.sol
THREADS=1 NOTREE=1 ODDSTRIDE=11 QUIET=1 timeout 120 nice -n 10 $T/lift $K/prism3.txt meta:11:8:10 3 9 40 1 8 $K/prism_m11_8_10.sol
THREADS=1 NOTREE=1 ODDSTRIDE=16 QUIET=1 timeout 120 nice -n 10 $T/lift $K/mob8.txt meta:16:4:7 3 9 40 2 8 $K/mob8_m16_4_7.sol
timeout 120 nice -n 10 $T/score48 $K/mob8_m16_4_7.sol.edges 3 9
