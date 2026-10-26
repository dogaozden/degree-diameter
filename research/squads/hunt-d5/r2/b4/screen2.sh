#!/bin/bash
# phase 1 screen: 3+3 bases over meta groups of order 202..215, 30 s each, seed 11
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/b4
T=../../tools
export OMP_NUM_THREADS=1 THREADS=1
run() { # tag group base seed secs
  o=out/$1_$(echo $2 | tr ':' '_')_$(basename $3 .txt)_s$4.sol
  res=$(timeout $(( $5 + 20 )) nice -n 10 $T/flift $3 $2 7 5 $5 $4 8 $o 2>&1 | grep RESULT)
  echo "$1 $2 $3 seed=$4 secs=$5 :: $res $(date +%T)"
}
for g in meta:29:7:7 meta:41:5:10 meta:17:12:4 meta:13:16:5 meta:7:30:2 meta:70:3:51 meta:14:15:9 meta:51:4:4; do
  run Q1 $g base33_Q2.txt 11 30
done
echo ALLDONE $(date +%T)
