#!/bin/bash
# usage: run2.sh LINE_NUMBER CPUSECS SEED   (p = 2, lines from cand2.txt; tables cached in tab2/)
D6=/home/user/degree-diameter/research/squads/beyond14/r2/d06
OC=/home/user/degree-diameter/research/frontier/beyond14/ownsmall
cd $D6; mkdir -p tab2 sols2 logs2
read N s < <(sed -n "$1p" cand2.txt)
tag=$(echo "L$1_${s}" | tr ':/' '__')
T=$D6/tab2/$tag.txt
if [ ! -s $T ]; then timeout 80 nice -n 10 env THREADS=1 python3 $OC/mktab.py $T "$s" > /dev/null 2>&1 || { echo "$N $s TABFAIL"; exit 1; }; fi
timeout 100 nice -n 10 env THREADS=1 D=14 ${START:+START=$START} $OC/salift_s 2 $T 1 ${3:-1} $2 10 0.3 $D6/sols2/$tag.sol > logs2/$tag.s${3:-1}.log 2>&1
echo "$N $s :: $(tail -1 logs2/$tag.s${3:-1}.log) :: $(grep -c FOUND logs2/$tag.s${3:-1}.log) found"
