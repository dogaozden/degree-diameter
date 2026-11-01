#!/bin/bash
# N m k r o : exhaustive Haar search (D=8, d=4) up to automorphism; appends "N m k r o min M lowcount C seconds S"
T=/home/user/degree-diameter/research/squads/b48/tools
cd "$(dirname "$0")"
[ -e err_$2_$3_$4.txt ] && exit 0
[ "$2" -le 5 ] && exit 0
: > err_$2_$3_$4.txt
t0=$(date +%s)
python3 $T/exh_meta.py $2 $3 $4 | LIMIT=2 ONLYLOW=1 nice -n 5 $T/flift $T/bases/dipole4.txt meta:$2:$3:$4 4 8 eval > low_$2_$3_$4.txt 2> err_$2_$3_$4.txt
mn=$(awk '{print $NF}' err_$2_$3_$4.txt | tail -1)
echo "$1 $2 $3 $4 $5 min $mn low $(wc -l < low_$2_$3_$4.txt) sec $(( $(date +%s) - t0 ))" >> results.txt
