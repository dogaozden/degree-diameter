#!/bin/bash
# usage: run.sh SEED M K R OUT [SECS]; one hmeta_sidon run, THREADS=1, SIDON=1, K<=64
D=/home/user/degree-diameter/research/squads/raise10/r4/h05
S=${6:-78}
THREADS=1 SIDON=1 timeout -s KILL 100 nice -n 10 $D/hmeta_sidon 6 10 $S $1 64 $D/$5 $2 $3 $4 > $D/$5.log 2>&1
tail -2 $D/$5.log
