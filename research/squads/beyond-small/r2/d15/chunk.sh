#!/bin/bash
# usage: chunk.sh IN_STATE OUT_STATE OUT_VALID SECS SEED TEMP WT
# runs one annealing chunk, then verifies the valid output with apsp (all-pairs) if it beats the best so far
D=/home/user/degree-diameter/research/squads/beyond-small
cd "$(dirname "$0")"
timeout 100 nice -n 10 ./anneal $D/data/d16D5_n33792.edges 6 "$4" "$5" "$6" 1.5 "$1" "$2" "$3" "$7" 2>&1 | tail -2
n=$(wc -l < "$3")
n=$((33792 + n))
if [ ! -f best_n.txt ] || [ "$n" -gt "$(cat best_n.txt)" ]; then
  timeout 100 nice -n 10 python3 $D/director/merge_hubs.py $D/data/d16D5_n33792.edges cand_n$n.edges "$3" >/dev/null
  r=$(timeout 100 nice -n 10 $D/bin/apsp cand_n$n.edges 17 5 | tail -1)
  echo "$r"
  if echo "$r" | grep -q "RESULT VALID"; then echo $n > best_n.txt; cp "$3" best_hubs.txt; rm -f best_n*.edges.prev; ls cand_n*.edges | grep -v "cand_n$n.edges" | xargs -r rm -f; fi
else
  echo "valid hubs $n (not above best $(cat best_n.txt))"
fi
