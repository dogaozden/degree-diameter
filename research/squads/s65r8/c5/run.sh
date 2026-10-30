#!/bin/bash
# card c5, round s65r8: exhaustive haarex3 over r8_list_4.txt, one process at a time.
# start new groups only before SOFT (11:07:00 UTC); cap each run at HARD (11:12:30 UTC).
cd /home/user/degree-diameter/research/squads/s65r8/c5
TOOLS=/home/user/degree-diameter/research/s65/tools
LIST=/home/user/degree-diameter/research/s65/haar/r8_list_4.txt
SOFT=$(date -u -d "2026-10-30 11:07:00" +%s)
HARD=$(date -u -d "2026-10-30 11:12:30" +%s)
: > table.txt
while read ID; do
  [ -z "$ID" ] && continue
  O=${ID%_*}; I=${ID#*_}
  NOW=$(date -u +%s)
  if [ "$NOW" -ge "$SOFT" ]; then echo "$ID | NOT REACHED (soft deadline) | - | - | -" >> table.txt; continue; fi
  EXP=$(gap -q -c "K:=SmallGroup($O,$I);; FN:=\"hx_${O}_${I}.txt\";;" $TOOLS/haarex2.g 2>&1 | grep EXPORTED)
  REM=$(( HARD - $(date -u +%s) )); T=600; [ "$REM" -lt "$T" ] && T=$REM
  timeout $T nice -n 10 $TOOLS/haarex3 hx_${O}_${I}.txt > h${O}_${I}.log 2>&1
  RC=$?
  rm -f hx_${O}_${I}.txt
  if grep -q '^DONE' h${O}_${I}.log; then
    D=$(grep '^DONE' h${O}_${I}.log)
    P=$(echo "$D" | sed -n 's/.*pairs=\(0\.\.[0-9]*\).*/\1/p')
    A=$(echo "$D" | sed -n 's/.*Acovered=\([0-9]*\).*/\1/p')
    V=$(echo "$D" | sed -n 's/.*valid=\([0-9]*\).*/\1/p')
    STAT="$P"
  else
    LAST=$(grep '^PAIR' h${O}_${I}.log | tail -1 | awk '{print $2}')
    A="?"; V="?"
    STAT="TIMEOUT(rc=$RC) last PAIR ${LAST:-none}"; P="0..${LAST:-none}"
  fi
  echo "$ID | ${EXP:-no export line} | $STAT | Acovered=$A | valid=$V" >> table.txt
  if grep -q '^VALID' h${O}_${I}.log; then
    echo "*** RECORD CANDIDATE $ID ***" >> record_candidates.txt; grep '^VALID' h${O}_${I}.log >> record_candidates.txt
  fi
  grep '^ASIDE' h${O}_${I}.log | sed "s/^/$ID /" >> aside.txt
done < $LIST
echo ALLDONE >> table.txt
