#!/bin/bash
# verifyA.sh SIDEFILE_SWAP : convert swapped side-A orbits to global ids, build (17,5) graph with B from startB, run apsp.
cd "$(dirname "$0")"
S=$1
awk '{s=""; for(i=1;i<=NF;i++) s=s ($i+16896) " "; print s}' "$S" > A_global.txt
timeout 100 nice -n 10 python3 ../../graphs/build_d17D5_hubs.py out.edges --orbits A_global.txt ../startB.txt
timeout 100 nice -n 10 ../../bin/apsp out.edges 17 5
