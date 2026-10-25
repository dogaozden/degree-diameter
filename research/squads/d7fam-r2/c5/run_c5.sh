#!/bin/bash
# sequential: 3 annealer runs (one process at a time), each scored by mirror_build2.py
cd /home/user/degree-diameter/research/squads/d7fam-r2/c5
SQ=/tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq
run() {  # name seed cmax T
  name=$1; seed=$2; cmax=$3; T=$4
  mkdir -p runs/$name
  timeout 400 nice -n 15 python3 mirror_sa5c.py $seed runs/$name --init $SQ/state_q13_F21.npz --pool 20000 --cmax $cmax --m 16 --sample 400 --T $T --secs 200 --rfile $SQ/R_q13.npy --hex $SQ/hex_q13.bin --sfile $SQ/S_q13.npy > runs/$name.log 2>&1 &
  PEAK=0
  while true; do
    for P in $(pgrep -f "mirror_sa5c.py $seed runs/$name "); do
      R=$(ps -o rss= -p $P 2>/dev/null | tr -d ' '); [ -n "$R" ] && [ "$R" -gt "$PEAK" ] && PEAK=$R
    done
    kill -0 $! 2>/dev/null || break
    sleep 1
  done
  echo "$name peak RSS KB: $PEAK" >> runs/mem.txt
  timeout 400 nice -n 15 python3 mirror_build2.py runs/$name/best.npz 1 runs/${name}_score $SQ/hex_q13.bin $SQ/S_q13.npy > runs/$name.score.txt 2>&1
  echo "$name scorer exit $?" >> runs/mem.txt
}
run A 11 48 0.05
run B 12 40 0.1
run C 13 44 0.05
echo DONE >> runs/mem.txt
