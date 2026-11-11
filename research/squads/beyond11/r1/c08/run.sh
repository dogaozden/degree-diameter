#!/bin/bash
# usage: run.sh "k m f" fam p n seed   (d=13, D=9, 60 s, K=4); one heavy process; logs to c08/runs/
K_M_F="$1"; FAM="$2"; P="$3"; N="$4"; SEED="$5"
TAG=$(echo "$K_M_F" | tr ' ' '-')_${FAM}_${P}_${N}_s${SEED}
D=/home/user/degree-diameter/research/squads/beyond11/r1/c08
mkdir -p $D/runs $D/sols
OUT=$D/sols/$TAG.txt
ORBIT="$K_M_F" THREADS=1 timeout 105 nice -n 10 /home/user/degree-diameter/research/frontier/beyond11/bin/haar_big0 13 9 60 $SEED 4 $OUT $FAM $P $N > $D/runs/$TAG.log 2>&1
echo "exit=$? $TAG $(grep -o 'RESULT.*' $D/runs/$TAG.log | tail -1) start: $(grep -o 'mu=[0-9.]*' $D/runs/$TAG.log | head -1)"
