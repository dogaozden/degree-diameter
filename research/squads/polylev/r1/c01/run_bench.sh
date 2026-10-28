#!/bin/bash
# card c01 benchmark: plain domlocal vs clause-weighting cwlocal, 300 s each, sequential (one thread).
cd /home/user/degree-diameter/research/squads/polylev/r1/c01
T=/home/user/degree-diameter/research/theorems/polylev
H3=$T/hex/hex_q3.bin; H7=$T/hex/hex_q7.bin
run() { # name hex side k binary extra...
  local name=$1 hex=$2 side=$3 k=$4 bin=$5; shift 5
  timeout 400 nice -n 10 $bin $hex $side $k 2 1 300 $PWD/out_${name}.bin "$@" > log_${name}.txt 2> err_${name}.txt
  echo "$name exit $?" >> bench_status.txt
}
run plain_q3_lines_k11 $H3 lines 11 ./domlocal_plain
run cw_q3_lines_k11 $H3 lines 11 ./cwlocal - 1000
run plain_q3_lines_k12 $H3 lines 12 ./domlocal_plain
run cw_q3_lines_k12 $H3 lines 12 ./cwlocal - 1000
run plain_q7_points_k40 $H7 points 40 ./domlocal_plain
run cw_q7_points_k40 $H7 points 40 ./cwlocal - 1000
run plain_q7_points_k43 $H7 points 43 ./domlocal_plain
run cw_q7_points_k43 $H7 points 43 ./cwlocal - 1000
echo done >> bench_status.txt
