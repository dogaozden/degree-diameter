#!/bin/bash
# card c8: exhaustive haarex3 over r8_list_7.txt, one process at a time, 35-minute box
cd /home/user/degree-diameter/research/squads/s65r8/c8
START=$(cat START)
LIST=/home/user/degree-diameter/research/s65/haar/r8_list_7.txt
TOOLS=/home/user/degree-diameter/research/s65/tools
while read ID; do
  [ -z "$ID" ] && continue
  NOW=$(date +%s); EL=$((NOW-START))
  if [ $EL -ge 1800 ]; then echo "STOP-NEW $ID elapsed=$EL" >> progress.txt; break; fi
  ORDER=${ID%_*}; GID=${ID#*_}
  REM=$((2100-EL)); TO=600; [ $REM -lt 600 ] && TO=$REM
  echo "START $ID at elapsed=$EL timeout=$TO" >> progress.txt
  gap -q -c "K:=SmallGroup($ORDER,$GID);; FN:=\"hx_${ORDER}_${GID}.txt\";;" $TOOLS/haarex2.g > exp_${ORDER}_${GID}.gaplog 2>&1
  if [ ! -s hx_${ORDER}_${GID}.txt ]; then echo "EXPORT-FAIL $ID" >> progress.txt; continue; fi
  EXP=$(grep -h EXPORTED exp_${ORDER}_${GID}.gaplog | head -1)
  echo "$EXP" > structure_${ORDER}_${GID}.txt
  timeout $TO nice -n 10 $TOOLS/haarex3 hx_${ORDER}_${GID}.txt > h${ORDER}_${GID}.log 2>&1
  RC=$?
  rm -f hx_${ORDER}_${GID}.txt
  DONE=$(grep -h '^DONE' h${ORDER}_${GID}.log | tail -1)
  echo "END $ID rc=$RC ${DONE:-NO-DONE} elapsed=$(( $(date +%s)-START ))" >> progress.txt
  grep -h 'VALID S' h${ORDER}_${GID}.log >> progress.txt 2>/dev/null
done < $LIST
echo "ALLDONE elapsed=$(( $(date +%s)-START ))" >> progress.txt
