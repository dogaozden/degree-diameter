#!/bin/bash
# run_one.sh TAG m k r SEED CPUSECS T0 [START.best]
# builds the Z_m x|_r Z_k table, then one salift_s run (p = 2, D = 14); prints the salift summary line.
cd /home/user/degree-diameter/research/squads/beyond14/r3/e02
S=/home/user/degree-diameter/research/frontier/beyond14/ownsmall/salift_s
T=tab_$1.txt
[ -s "$T" ] || timeout 105 nice -n 10 env THREADS=1 python3 mkt.py "$T" "$2" "$3" "$4" >/dev/null
if [ -n "$8" ]; then ST="START=$8"; else ST="X=1"; fi
timeout 105 nice -n 10 env THREADS=1 D=14 $ST $S 2 "$T" 1 "$5" "$6" "$7" 0.3 "$1"_s$5.sol 2>&1 | tail -2
echo "tag=$1 seed=$5 best=$(head -1 "$1"_s$5.sol.best 2>/dev/null) sol=$(ls "$1"_s$5.sol 2>/dev/null)"
