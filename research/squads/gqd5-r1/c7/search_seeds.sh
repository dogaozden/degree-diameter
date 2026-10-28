#!/bin/bash
# retry random hub choices / hub graph Y until apsp reports RESULT VALID (card c7)
cd /home/user/degree-diameter/research/squads/gqd5-r1/c7
for s in $(seq $1 $2); do
  python3 go.py tmp_seed.edges $s > /dev/null
  r=$(cd /home/user/degree-diameter/research/theorems/d5gq && ./apsp /home/user/degree-diameter/research/squads/gqd5-r1/c7/tmp_seed.edges 8 5 | tail -1)
  case "$r" in "RESULT VALID"*) echo "seed $s: $r"; mv tmp_seed.edges best.edges; echo "$s" > best_seed.txt; exit 0;; esac
done
echo "no valid seed in $1..$2"
rm -f tmp_seed.edges
