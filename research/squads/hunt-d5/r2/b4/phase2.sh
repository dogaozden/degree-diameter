#!/bin/bash
# phase 2: best three screen cells, 60 s, second seed
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/b4
T=../../tools
export OMP_NUM_THREADS=1 THREADS=1
run() { # tag group base seed secs
  o=out/$1_$(echo $2 | tr ':' '_')_$(basename $3 .txt)_s$4.sol
  res=$(timeout $(( $5 + 20 )) nice -n 10 $T/flift $3 $2 7 5 $5 $4 8 $o 2>&1 | grep RESULT)
  echo "$1 $2 $3 seed=$4 secs=$5 :: $res $(date +%T)"
}
run P2 meta:62:5:33 base22_a3.txt 12 60
run P2 meta:35:9:11 base22_a3.txt 12 60
run Q2 meta:41:5:10 base33_Q2.txt 12 60
echo ALLDONE $(date +%T)
