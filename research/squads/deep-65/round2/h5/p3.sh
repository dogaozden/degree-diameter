#!/bin/bash
# usage: p3.sh GROUPIDX A "SEEDS" SECS  -> appends "g<idx> a<A> seed<s> best<cost> bad<cost/2>" to logs/p3.log
cd /home/user/degree-diameter/research/squads/deep-65/round2/h5
for s in $3; do
  out=$(timeout 40 nice -n 10 ./bin/tabu3 groups/sg_147_$1.txt $2 $s 100000000 4 $4 edges/p3_g$1_a$2_s$s.edges 600 | grep RESULT)
  best=$(echo "$out" | awk '{print $3}')
  echo "g$1 a$2 seed$s cost $best bad $((best/2))" >> logs/p3.log
done
