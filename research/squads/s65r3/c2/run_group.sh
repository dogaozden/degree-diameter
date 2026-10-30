#!/bin/bash
# usage: run_group.sh ORDER_ID   (e.g. 360_88); runs haarex2 on SmallGroup(order,id) with a 240 s cap
cd /home/user/degree-diameter/research/squads/s65r3/c2
ID="$1"; ORD="${ID%%_*}"; SID="${ID##*_}"
FN="hx_${ID}.txt"; LOG="h${ID}.log"
line=$(gap -q -c "K:=SmallGroup(${ORD},${SID});; FN:=\"${FN}\";;" /home/user/degree-diameter/research/s65/tools/haarex2.g 2>&1 | grep EXPORTED)
STRUCT=$(echo "$line" | sed -E 's/.*gens=[0-9]+ //')
timeout 240 nice -n 10 env THREADS=1 /home/user/degree-diameter/research/s65/tools/haarex2 "$FN" > "$LOG" 2>&1
echo "EXIT $?" >> "$LOG"
TOTAL=$(awk '/pair classes=/{sub(/.*pair classes=/,""); sub(/,.*/,""); print; exit}' "$LOG")
if grep -q '^DONE' "$LOG"; then
  FIN=yes; DONEP="$TOTAL/$TOTAL"
  SETS=$(grep '^DONE' "$LOG" | sed -E 's/.*sets=([0-9]+).*/\1/')
  MINA=$(grep '^DONE' "$LOG" | sed -E 's/.*minA=([0-9]+).*/\1/')
else
  FIN=no; LAST=$(grep '^PAIR' "$LOG" | tail -1 | awk '{print $2}')
  DONEP="last PAIR idx ${LAST:--}/$TOTAL"
  SETS=$(grep '^PAIR' "$LOG" | sed -E 's/.*sets=([0-9]+).*/\1/' | awk '{s+=$1} END{print s+0}')
  MINA=$(grep '^PAIR' "$LOG" | sed -E 's/.*minA=([0-9]+).*/\1/' | sort -n | head -1)
fi
VALID=$(grep -c '^VALID' "$LOG")
MINB=$(grep '^ASIDE' "$LOG" | sed -E 's/.*Bunc=([0-9]+).*/\1/' | sort -n | head -1); MINB=${MINB:--}
echo "${ID} | ${STRUCT} | ${FIN} | ${DONEP} | ${SETS} | ${VALID} | ${MINA:--} | ${MINB}" >> table.txt
rm -f "$FN"
echo "FINISHED ${ID} ${FIN}"
