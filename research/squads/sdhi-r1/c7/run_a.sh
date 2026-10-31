#!/bin/bash
cd /home/user/degree-diameter/research/squads/sdhi-r1/c7
export THREADS=1
ORDS=2,6 SECS=20 STALL=300 timeout 300 nice -n 10 ./sdhi 5 7 psl 8 meta 3 2 2 > out_psl8_S3.txt 2>&1
ORDS=2,6 SECS=20 STALL=300 timeout 300 nice -n 10 ./sdhi 5 7 psl 7 meta 5 2 4 > out_psl7_D10.txt 2>&1
ORDS=2,6 SECS=20 STALL=300 timeout 300 nice -n 10 ./sdhi 5 7 sl 5 meta 7 2 6 > out_sl5_D14.txt 2>&1
echo ALLDONE > done_a.txt
