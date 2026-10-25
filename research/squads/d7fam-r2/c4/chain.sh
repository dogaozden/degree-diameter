#!/bin/bash
# runs 3 annealer runs one at a time (300 s each), monitors RSS, then scores each best.npz
cd /home/user/degree-diameter/research/squads/d7fam-r2/c4
run() { # seed T name
  local seed=$1 T=$2 name=$3
  timeout 400 nice -n 15 python3 mirror_sa5c.py $seed run_$name --init /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/state_k12_r6c3.npz --pool 40000 --m 16 --sample 400 --T $T --secs 300 --rfile /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/R_q11.npy --hex /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/hex_q11.bin --sfile /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/S_q11.npy > run_$name.log 2>&1 &
  sleep 1; local P=$(pgrep -f "mirror_sa5c.py $seed run_$name" | head -1); local PEAK=0
  while kill -0 $P 2>/dev/null; do R=$(ps -o rss= -p $P 2>/dev/null | tr -d ' '); [ -n "$R" ] && [ "$R" -gt "$PEAK" ] && PEAK=$R; if [ "$PEAK" -gt 1500000 ]; then kill $P; echo "KILLED over mem" >> run_$name.log; fi; sleep 0.5; done
  echo "PEAK_RSS_KB $PEAK" >> run_$name.log
  timeout 400 nice -n 15 python3 mirror_build2.py run_$name/best.npz 1 score_$name /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/hex_q11.bin /tmp/claude-0/-home-user-degree-diameter/0ecf9576-c77c-5462-b736-5bb1ddd9e678/scratchpad/w/sq/S_q11.npy > score_$name.log 2>&1
  echo "done $name $(date)" >> chain_status.log
}
run 1 0.1 s1
run 2 0.1 s2
run 3 0.05 s3
echo ALLDONE >> chain_status.log
