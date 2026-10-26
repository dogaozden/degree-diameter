#!/bin/bash
# phase 1 screen: 2+2 bases over meta groups of order 303..320, 30 s each, seed 11
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/b4
T=../../tools
export OMP_NUM_THREADS=1 THREADS=1
run() { # tag group base seed secs
  o=out/$1_$(echo $2 | tr ':' '_')_$(basename $3 .txt)_s$4.sol
  res=$(timeout $(( $5 + 20 )) nice -n 10 $T/flift $3 $2 7 5 $5 $4 8 $o 2>&1 | grep RESULT)
  echo "$1 $2 $3 seed=$4 secs=$5 :: $res $(date +%T)"
}
for g in meta:31:10:15 meta:13:24:7 meta:104:3:9 meta:105:3:16 meta:35:9:11 meta:80:4:3 meta:62:5:33 meta:103:3:46; do
  run P1 $g base22_a3.txt 11 30
done
echo ALLDONE $(date +%T)
