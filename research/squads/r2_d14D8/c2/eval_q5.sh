#!/bin/bash
# q=5 lift check of the level family: optimized h (bundle SA, mode 1) vs random h, same a,b seeds, exact lifteval all
cd /home/user/degree-diameter/research/squads/r2_d14D8/c2
LE=/home/user/degree-diameter/research/squads/cells/d14D8_work/lifteval
for k in 5 6 7; do
  for s in 1 2 3; do
    for mode in opt rand; do
      if [ $mode = opt ]; then H=h_q5_k${k}_m1.txt; else H=rand:$((100+s)); fi
      B=base_q5_k${k}_${mode}_s${s}.txt
      python3 mk_h.py 5 $k $H $((10+s)) $((20+s)) $B > /dev/null
      R=$(timeout 900 nice -n 10 $LE $B 8 all 2>/dev/null)
      echo "q=5 k=$k m=$((5*k)) h=$mode seed=$s : $R"
    done
  done
done
echo EVAL_DONE
