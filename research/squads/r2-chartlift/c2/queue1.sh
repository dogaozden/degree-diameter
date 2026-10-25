#!/bin/bash
# squad c2, queue 1: sequential chart_anneal2 runs (one process at a time). Logs and charts in c2/runs/.
C=/home/user/degree-diameter/research/squads/r2-chartlift/c2
cd /home/user/degree-diameter/research/theorems/chartlift || exit 1
run() {   # tag init(1=start from k5q3_pd112) T0 TAU seed secs
  local tag=$1 init=$2 t0=$3 tau=$4 seed=$5 secs=$6
  if [ "$init" = 1 ]; then
    INIT=r3/k5q3_pd112.txt T0=$t0 TAU=$tau STALL=60000 timeout 900 nice -n 10 $C/chart_anneal2 tables/gf3.txt 5 $secs $seed 1 100 100 $C/runs/$tag.txt > $C/runs/$tag.log 2>&1
  else
    T0=$t0 TAU=$tau STALL=60000 timeout 900 nice -n 10 $C/chart_anneal2 tables/gf3.txt 5 $secs $seed 1 100 100 $C/runs/$tag.txt > $C/runs/$tag.log 2>&1
  fi
  echo "$tag $(tail -n 1 $C/runs/$tag.log)" >> $C/runs/summary.txt
}
run a_T4_tau15k_s1 1 4 15000 1 200
run b_rand_T8_tau40k_s11 0 8 40000 11 250
run a_T8_tau40k_s2 1 8 40000 2 200
run a_T12_tau15k_s3 1 12 15000 3 200
echo DONE >> $C/runs/summary.txt
