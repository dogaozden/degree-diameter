#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c3
run(){ tag=$1; base=$2; shift 2; b=$(basename $base .txt); timeout 600 nice -n 10 ./lift search $base 5 120 7 8 runs/L_${tag}_${b}.sol "$@" > runs/L_${tag}_${b}.log 2>&1; }
export -f run
printf '%s\n' "Z11Z4|bases/h8_r1.txt|meta 11 4 10" "Z11Z4|bases/h8_r2.txt|meta 11 4 10" "A5|bases/h6_K66.txt|psl 5" "Z13Z3|bases/h9_r2.txt|meta 13 3 3" | xargs -P 2 -I{} bash -c 'IFS="|" read -r t b g <<< "{}"; run "$t" "$b" $g'
echo DONE
