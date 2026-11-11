#!/bin/bash
# usage: run1.sh n lambda secs seed tag  (anneal of Tutte 8-cage lift, D=15 unless D env set)
F=/home/user/degree-diameter/research/frontier; L=$F/beyond15/lsym; K=/home/user/degree-diameter/research/squads/beyond15/r3/k01
env THREADS=1 T0=2 T1=0.05 L=1200 timeout 100 nice -n 10 $F/bin/liftsym $L/tutte8.txt $L/tutte8.perm $1 $2 ${D:-15} $3 $4 $K/out/$5 2>&1 | grep -E "RESULT|start" | tr '\n' ' '; echo
