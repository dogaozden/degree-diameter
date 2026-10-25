#!/bin/bash
# sequential runs (single thread); each: annealer then scorer on its best.npz
cd /home/user/degree-diameter/research/squads/d7fam-r1/c4
SQ=/tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq
# args: name seed T cmax init secs
run() {
  name=$1; seed=$2; T=$3; cmax=$4; init=$5; secs=$6
  if [ "$init" = "scratch" ]; then initarg=""; else initarg="--init $init"; fi
  timeout 900 nice -n 15 python3 mirror_sa5.py $seed /home/user/degree-diameter/research/squads/d7fam-r1/c4/out_$name $initarg --secs $secs --T $T --pool 19000 --cmax $cmax --m 8 --sample 150 --rfile $SQ/R_q7.npy --hex $SQ/hex_q7.bin --sfile $SQ/S_q7.npy > /home/user/degree-diameter/research/squads/d7fam-r1/c4/log_$name.txt 2>&1
  sc=$(timeout 900 nice -n 15 python3 mirror_build2.py /home/user/degree-diameter/research/squads/d7fam-r1/c4/out_$name/best.npz 1 /home/user/degree-diameter/research/squads/d7fam-r1/c4/score_$name /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/hex_q7.bin /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/S_q7.npy 2>&1 | tail -1)
  echo "$name seed=$seed T=$T cmax=$cmax init=$init :: $sc" >> /home/user/degree-diameter/research/squads/d7fam-r1/c4/summary.txt
}
run A 11 0.3 30 scratch 220
run B 12 0.5 40 /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/state_q7_F7.npz 220
run C 13 0.5 20 scratch 220
run D 14 0.3 20 /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/state_q7_F7.npz 220
echo DONE >> /home/user/degree-diameter/research/squads/d7fam-r1/c4/summary.txt
