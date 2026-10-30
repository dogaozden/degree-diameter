#!/bin/bash
# re-anneal the three best sweep cards (order 1316) for 300 s each, one at a time
cd /home/user/degree-diameter/research/squads/bh5b-r2/c3
for f in sg1316_5_3_3 sg1316_6_1_1 sg1316_6_2_2; do
  echo "START $f $(date)"
  SA=1 SECS=300 SEED=2 timeout 900 nice -n 10 ./dcenum dc/$f.dc2 7 5 dc/re_$f.edges 2>/dev/null | tail -1 | sed "s/^/$f: /"
  echo "DONE $f $(date)"
done
echo REANNEAL_ALLDONE $(date)
