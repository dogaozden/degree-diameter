#!/bin/bash
# Card c4: (7,10) ORBIT "3 2 1", 150 s seeds, up to 6 per group, ORBW=3 sticky after a seed ends at 1 or 2.
# usage: step.sh MAXSECS   (runs seeds while elapsed + 160 s <= MAXSECS; state kept in state.txt)
C=/home/user/degree-diameter/research/squads/r5/c4
B=/tmp/claude-0/-home-user-degree-diameter/2744c2da-0db8-5a6f-87c3-01a128c9c95e/scratchpad/bin
MAX=$1
ST=$C/state.txt
LOG=$C/summary.txt
[ -f $ST ] || echo "0 1 0 0" > $ST   # gi si orbw_sticky solved
GRPS=( "g1|prod sl 3 sl 7 139" "g2|sl 17 229" "g3|prod sl 5 sl 9 13" "g4|psl 131 1" )
read gi si ow solved < $ST
start=$(date +%s)
while :; do
  if [ "$gi" -ge 4 ]; then echo "ALL GROUPS DONE" | tee -a $LOG; break; fi
  if [ "$solved" -eq 1 ] || [ "$si" -gt 6 ]; then
    gi=$((gi+1)); si=1; solved=0
    echo "0 1 0 0" | awk -v g=$gi -v o=$ow '{print g, 1, o, 0}' > $ST
    read gi si ow solved < $ST
    continue
  fi
  el=$(( $(date +%s) - start ))
  if [ $((el + 160)) -gt "$MAX" ]; then break; fi
  IFS='|' read tag grp <<< "${GRPS[$gi]}"
  out=$C/${tag}_s${si}
  if [ "$ow" -eq 1 ]; then export ORBW=3; else unset ORBW; fi
  ORBIT="3 2 1" timeout 250 nice -n 10 $B/haar_sym 7 10 150 $si 8 $out.txt $grp > $out.log 2>&1
  best=$(grep -o 'best=[0-9]*' $out.log | tail -1 | cut -d= -f2)
  [ -z "$best" ] && best=NA
  echo "$tag [$grp] seed=$si ORBW=${ORBW:-unset} best=$best  $(grep -o 'Fix[^,]*' $out.log | head -1)" | tee -a $LOG
  if [ "$best" = "0" ]; then
    solved=1
    echo "SOLVED $tag seed $si -> $out.txt" | tee -a $LOG
  fi
  if [ "$best" = "1" ] || [ "$best" = "2" ]; then ow=1; fi
  si=$((si+1))
  echo "$gi $si $ow $solved" > $ST
done
echo "state: $(cat $ST)"
