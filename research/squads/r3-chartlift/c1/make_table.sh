#!/bin/bash
# builds c1/table.tsv: base  group  class  m  best_cost  (from runs/sweep_cls*/ and runs/cal/)
cd /home/user/degree-diameter/research/squads/r3-chartlift/c1
echo -e "run\tclass\tm\tbest_cost\titers"
for f in runs/sweep_cls*/*.out runs/cal/*.out; do
  [ -f "$f" ] || continue
  tag=$(basename "$f" .out)
  cls=$(echo "$f" | sed -n 's/.*sweep_cls\([0-9]*\).*/\1/p'); [ -z "$cls" ] && cls=1
  line=$(grep -h "best_cost=" "$f" | tail -n 1)
  m=$(echo "$line" | sed -n 's/.* m=\([0-9]*\) .*/\1/p')
  bc=$(echo "$line" | sed -n 's/.*best_cost=\([0-9]*\).*/\1/p')
  it=$(echo "$line" | sed -n 's/.*iters=\([0-9]*\).*/\1/p')
  echo -e "$tag\t$cls\t${m:-?}\t${bc:-NA}\t${it:-?}"
done
