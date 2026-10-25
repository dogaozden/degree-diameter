#!/bin/bash
# Card c5: fake (controller ceiling) sweep with free diagonals. Per base: descending order levels; stop a base after the first level with a success.
D=/home/user/degree-diameter/research/d12D5
C=/home/user/degree-diameter/research/squads/d12D5-r2/c5
cd $C
M=$D/mlift_ejoint2
for b in 1 2 3; do
  for lvl in "40 g40c g40p" "39 g39c g39m" "38 g38" "37 g37" "36 g36c g36a g36b g36d" "35 g35"; do
    set -- $lvl; ord=$1; shift; ok=0
    for t in "$@"; do
      out=fake/fk_b${b}_${t}.log
      FAKE=1 DIAGBT=1 timeout 300 nice -n 10 $M $C/base_k2_$b.txt $C/tables/$t.txt 10 1 2 1.0 > $out 2>&1
      line=$(grep -o 'best_cost=[0-9]*' $out | head -1)
      echo "base=$b table=$t order=$ord $(head -1 $out) ${line:-NOLINE}" | tee -a fake/SUMMARY.txt
      if [ "$line" = "best_cost=0" ]; then ok=1; fi
    done
    if [ $ok = 1 ]; then echo "base=$b ceiling order=$ord m=$((2*ord))" | tee -a fake/SUMMARY.txt; break; fi
  done
done
echo DONE | tee -a fake/SUMMARY.txt
