#!/bin/bash
# card c6: exhaustive haarex3 over hi_list_5.txt, one process at a time, time-boxed.
cd /home/user/degree-diameter/research/squads/s65r7/c6
LIST=/home/user/degree-diameter/research/s65/haar/hi_list_5.txt
TOOLS=/home/user/degree-diameter/research/s65/tools
START_NEW=$(date -u -d '2026-10-30 10:50:37' +%s)
HARD=$(date -u -d '2026-10-30 10:55:37' +%s)
while read ID; do
  now=$(date +%s)
  if [ "$now" -ge "$START_NEW" ]; then echo "STOP before $ID (time box)" >> run.out; break; fi
  ORDER=${ID%_*}; GID=${ID#*_}
  FN=hx_${ORDER}_${GID}.txt; LOG=h${ORDER}_${GID}.log
  STRUCT=$(gap -q -c "K:=SmallGroup($ORDER,$GID);; FN:=\"$FN\";;" $TOOLS/haarex2.g 2>/dev/null </dev/null | sed -n 's/^EXPORTED.* n=[0-9]* |Aut|=[0-9]* gens=[0-9]* //p')
  if ! grep -q '^DONE' "$LOG" 2>/dev/null; then
    rem=$((HARD - $(date +%s)))
    T=600; [ "$rem" -lt 600 ] && T=$rem
    if [ "$T" -le 5 ]; then echo "STOP before $ID (hard limit)" >> run.out; rm -f "$FN"; break; fi
    echo "START $ID at $(date -u +%H:%M:%S) timeout=$T" >> run.out
    timeout "$T" nice -n 10 $TOOLS/haarex3 "$FN" > "$LOG" 2>&1 </dev/null
  fi
  rm -f "$FN"
  grep '^VALID' "$LOG" > "VALID_${ORDER}_${GID}.txt" 2>/dev/null
  if [ -s "VALID_${ORDER}_${GID}.txt" ]; then echo "!!! RECORD CANDIDATE $ID: see c6/VALID_${ORDER}_${GID}.txt" >> run.out; else rm -f "VALID_${ORDER}_${GID}.txt"; fi
  DL=$(grep '^DONE' "$LOG")
  if [ -n "$DL" ]; then
    P=$(echo "$DL" | sed -n 's/.*pairs=0\.\.\([0-9]*\).*/\1/p')
    A=$(echo "$DL" | sed -n 's/.*Acovered=\([0-9-]*\).*/\1/p')
    V=$(echo "$DL" | sed -n 's/.*valid=\([0-9-]*\).*/\1/p')
    COV="0..$P"
  else
    LASTP=$(grep '^PAIR' "$LOG" | tail -1 | awk '{print $2}')
    A="partial:$(grep '^PAIR' "$LOG" | sed -n 's/.*acovers=\([0-9]*\).*/\1/p' | awk '$1>0{n++} END{print n+0}')"
    V=$(grep -c '^VALID' "$LOG")
    COV="0..${LASTP:-none} (TIMEOUT)"
  fi
  echo "$ID | $STRUCT | $COV | $A | $V" >> table.txt
  echo "DONE-GROUP $ID $DL" >> run.out
done < "$LIST"
echo "ALL-END $(date -u +%H:%M:%S)" >> run.out
