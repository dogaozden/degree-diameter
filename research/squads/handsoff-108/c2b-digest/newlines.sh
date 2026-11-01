#!/bin/bash
# prints scoreboard lines added since the last call (state in seen.count); flags cost 0 and records/ files
S=/home/user/degree-diameter/research/squads/handsoff-108
seen=$(cat $S/c2b-digest/seen.count 2>/dev/null || echo 0)
n=$(wc -l < $S/scoreboard.tsv)
if [ "$n" -gt "$seen" ]; then
  tail -n +$((seen+1)) $S/scoreboard.tsv | awk -F'\t' '{print substr($1,6,11), $2, "cost="$5, substr($3,1,70), "|", substr($7,1,120)}'
  echo $n > $S/c2b-digest/seen.count
fi
echo "records/: $(ls $S/records | wc -l) files; cost-0 scoreboard lines: $(awk -F'\t' 'NR>1 && $5==0' $S/scoreboard.tsv | wc -l)"
