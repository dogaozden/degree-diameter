#!/bin/bash
# card c1 of round r4-d11D5: sequential wpo runs (one heavy process at a time), time-boxed
cd /home/user/degree-diameter/research/squads/r4-d11D5/c1
P=/home/user/degree-diameter/research/d11D5
DEADLINE=$(( $(date +%s) + 2880 ))
run() {
  name=$1; start=$2; s=$3
  now=$(date +%s); left=$(( DEADLINE - now ))
  if [ $left -le 60 ]; then echo "SKIP $name (time box)"; return; fi
  cap=1500; [ $left -lt $cap ] && cap=$left
  echo "START $name $(date +%T) cap=$cap"
  timeout $cap nice -n 10 env SECS=600 SEED=$s OUT=out_$name.in OUT0=fail0_$name.in ./wpo $start > log_$name.txt 2>&1
  echo "END $name rc=$? $(date +%T) $(tail -1 log_$name.txt)"
}
run f5 $P/plus/best_f5.in 101
run g61 $P/plus/best_g61.in 102
run u602 $P/plus/best_u602.in 103
run d1s13 $P/inc/runs/d1_s13.in 104
run h71 $P/plus/best_h71.in 105
run h72 $P/plus/best_h72.in 106
run m81 $P/plus/best_m81.in 107
run m82 $P/plus/best_m82.in 108
run m83 $P/plus/best_m83.in 109
run v701 $P/plus/best_v701.in 110
run v702 $P/plus/best_v702.in 111
echo ALLDONE $(date +%T)
