#!/bin/bash
# usage: run_k.sh D Vlo Vhi k maxpat secs  -> appends to n06/log.txt
cd /home/user/degree-diameter/research/frontier/beyond15/lsym
ANNEAL=$6 THREADS=1 timeout 100 nice -n 10 python3 quotgen.py $1 $2 $3 $4 $4 "3 3 0-0,0-1,0-2,1-0,1-1,1-2,2-0,2-1,2-2" $5 $(( $4 * 7 + 1 )) 1 2>&1 | sed "s/^/D$1 /" >> /home/user/degree-diameter/research/squads/beyond15/r4/n06/log.txt
