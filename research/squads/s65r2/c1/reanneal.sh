#!/bin/bash
# re-anneal the 3 best (group, H, K) pairs of the sweep for 120 s each (seed 2), score the best edge lists
cd /home/user/degree-diameter/research/squads/s65r2/c1
mkdir -p best
grep "^RESULT" logs/sw_704_h2_d6.txt | grep -v " best 0 " | awk '{for(i=1;i<=NF;i++) if($i=="best") print $(i+1), $2}' | sort -n | head -3 > best/top3.txt
cat best/top3.txt
while read cost path; do
  base=$(basename $path .dc2); id=$(echo $base | sed -E 's/sg704_([0-9]+)_([0-9]+)_([0-9]+)/\1/')
  pa=$(echo $base | sed -E 's/sg704_([0-9]+)_([0-9]+)_([0-9]+)/\2/'); pb=$(echo $base | sed -E 's/sg704_([0-9]+)_([0-9]+)_([0-9]+)/\3/')
  d=best/g${id}_${pa}_${pb}; mkdir -p $d
  gap -q -c "ORDER:=704; H_ORDER:=2; OUTDIR:=\"$d\"; IDS:=[$id]; SKIPHAAR:=true;" sg_export.g > $d/gap.log 2>&1
  f=$d/sg704_${id}_${pa}_${pb}.dc2
  if [ ! -e "$f" ]; then echo "MISSING $f"; continue; fi
  SA=1 SECS=120 SEED=2 timeout 1200 nice -n 10 ./dcenum $f 6 5 best/g${id}_${pa}_${pb}.edges 2>&1 | tail -1 | tee -a best/reanneal.txt
  echo "cost-prior $cost group $id pair $pa $pb" >> best/reanneal.txt
  ./score65 best/g${id}_${pa}_${pb}.edges | tee -a best/score.txt
done < <(sed -E 's/^([0-9]+) (.*)$/\1 \2/' best/top3.txt)
echo "REANNEAL DONE $(date)"
