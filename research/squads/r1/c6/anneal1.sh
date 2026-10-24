#!/bin/bash
# anneal the best screened (group, orbit) pairs; one process at a time.  Lines: ORBIT|SEED|GROUP...|n
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
C=/home/user/degree-diameter/research/squads/r1/c6
cd $C
while IFS='|' read -r ORB SEED GRP; do
  [ -z "$ORB" ] && continue
  ot=$(echo "$ORB" | tr -d ' ')
  tag=$(echo "$GRP" | tr ' ' '_')
  ORBIT="$ORB" timeout 900 nice -n 10 $B/haar_sym 6 5 300 $SEED 8 $C/a_${tag}_${ot}_s${SEED}.txt $GRP > $C/logs/a_${tag}_${ot}_s${SEED}.log 2>&1
  echo "== $GRP | ORBIT=$ORB seed=$SEED :: $(grep -h -E 'RESULT|best=|VALID|wrote' $C/logs/a_${tag}_${ot}_s${SEED}.log | tail -3 | tr '\n' ' ')"
done <<'LIST'
3 2 0|1|psl 5 7
3 2 0|1|psl 9 1
2 3 0|1|sl 5 3
3 2 0|1|psl 3 31
LIST
