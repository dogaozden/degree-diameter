#!/bin/bash
# usage: run.sh SEED K GROUPTAG  (GROUPTAG: A = meta 2377 27 7 ; B = meta 1777 37 4)
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r3/g4
s=$1; K=$2; tag=$3
if [ "$tag" = A ]; then G="meta 2377 27 7 1"; else G="meta 1777 37 4 1"; fi
SAVEBEST=b_s$s.txt THREADS=1 timeout 105 nice -n 10 $B/haar_gen3s 6 9 90 $s $K OUT_s$s.txt $G > log_s$s.txt 2>&1
rc=$?
best=$(grep -o 'best=[0-9]*' log_s$s.txt | tail -1 | cut -d= -f2)
ev=$(grep -o 'evals=[0-9]*' log_s$s.txt | tail -1 | cut -d= -f2)
echo "$s | $K | $tag | ${best:-NA} | ${ev:-NA} | rc=$rc" >> seeds.txt
tail -1 seeds.txt
if [ -f OUT_s$s.txt ]; then echo "CORNER: OUT_s$s.txt exists (cost 0)"; fi
