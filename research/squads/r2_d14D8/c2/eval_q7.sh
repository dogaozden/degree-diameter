#!/bin/bash
# q=7 lift check of the level family: optimized h vs random h, lifteval r:200 first, exact all only if the sample passes
cd /home/user/degree-diameter/research/squads/r2_d14D8/c2
LE=/home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval
for k in 6 7; do
  for s in 1 2; do
    for mode in opt rand; do
      if [ $mode = opt ]; then H=h_q7_k${k}_m1.txt; else H=rand:$((200+s)); fi
      B=base_q7_k${k}_${mode}_s${s}.txt
      python3 mk_h.py 7 $k $H $((10+s)) $((20+s)) $B > /dev/null
      R=$(timeout 900 nice -n 10 $LE $B 8 r:200:7 2>/dev/null)
      echo "q=7 k=$k m=$((5*k)) h=$mode seed=$s r200: $R"
      if echo "$R" | grep -q "^COST 0 "; then
        R2=$(timeout 900 nice -n 10 $LE $B 8 all 2>/dev/null)
        echo "q=7 k=$k m=$((5*k)) h=$mode seed=$s all: $R2"
      fi
    done
  done
done
echo EVAL7_DONE
