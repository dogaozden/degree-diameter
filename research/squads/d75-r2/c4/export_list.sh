#!/bin/bash
# exports SmallGroup(N,ID) tables for the candidate list into c4/
cd /home/user/degree-diameter/research/squads/d75-r2/c4
for id in "$@"; do
  N=${id%_*}; I=${id#*_}
  timeout 600 nice -n 15 gap -q -c "N:=$N;; ID:=$I;; OUT:=\"/home/user/degree-diameter/research/squads/d75-r2/c4/g${N}_${I}.ht\";;" /home/user/degree-diameter/research/d75-raise/src/export.g > /dev/null 2>&1
  echo "$id $(head -1 g${N}_${I}.ht 2>/dev/null)"
done
