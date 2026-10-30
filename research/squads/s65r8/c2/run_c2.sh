#!/bin/bash
# Card c2, round s65r8: exhaustive haarex3 over r8_list_1.txt, one process at a time, in order.
D=/home/user/degree-diameter/research/squads/s65r8/c2
T=/home/user/degree-diameter/research/s65/tools
L=/home/user/degree-diameter/research/s65/haar/r8_list_1.txt
cd "$D" || exit 1
START=$(date +%s)
SOFT=$((START + 1800))   # no new group after 30 min
HARD=$((START + 2100))   # everything finished by 35 min
: > table.txt
: > valid_found.txt
while read -r id; do
  [ -z "$id" ] && continue
  now=$(date +%s)
  if [ "$now" -ge "$SOFT" ]; then echo "$id | not reached (time box) | - | - | -" >> table.txt; continue; fi
  ORDER=${id%_*}; ID=${id#*_}
  EXP=hx_${ORDER}_${ID}.txt
  gap -q -c "K:=SmallGroup($ORDER,$ID);; FN:=\"$EXP\";;" "$T/haarex2.g" > exp_${ORDER}_${ID}.out 2>&1
  struct=$(grep -o 'EXPORTED.*' exp_${ORDER}_${ID}.out | sed -E 's/.* gens=[0-9]+ //')
  if [ ! -s "$EXP" ]; then echo "$id | export failed | - | - | -" >> table.txt; continue; fi
  now=$(date +%s); tmo=$((HARD - now)); [ "$tmo" -gt 600 ] && tmo=600
  echo "START $id $(date +%T) timeout=$tmo" >> progress.txt
  timeout "$tmo" nice -n 10 "$T/haarex3" "$EXP" > h${ORDER}_${ID}.log 2>&1
  rc=$?
  rm -f "$EXP" exp_${ORDER}_${ID}.out
  LOG=h${ORDER}_${ID}.log
  echo "END $id $(date +%T) rc=$rc" >> progress.txt
  P=$(grep -o 'pair classes=[0-9]*' "$LOG" | head -1 | cut -d= -f2)
  last=$(grep '^PAIR ' "$LOG" | tail -1 | awk '{print $2}')
  done_line=$(grep '^DONE ' "$LOG")
  nvalid_lines=$(grep -c '^VALID' "$LOG")
  if [ -n "$done_line" ]; then
    cov=$(echo "$done_line" | grep -o 'pairs=[0-9]*\.\.[0-9]*' | cut -d= -f2)
    acov=$(echo "$done_line" | grep -o 'Acovered=[0-9]*' | cut -d= -f2)
    v=$(echo "$done_line" | grep -o 'valid=[0-9]*' | cut -d= -f2)
    cov="$cov (DONE)"
  else
    cov="0..${last:-none} of 0..${P:-?} (TIMEOUT, rc=$rc)"
    acov=$(grep '^PAIR ' "$LOG" | sed -E 's/.*acovers=([0-9]+).*/\1/' | awk '{s+=$1} END{print s+0}')"+ (partial)"
    v=$nvalid_lines
  fi
  echo "$id | $struct | $cov | $acov | $v" >> table.txt
  if [ "$nvalid_lines" -gt 0 ]; then
    echo "!!! RECORD CANDIDATE $id" >> valid_found.txt
    grep '^VALID' "$LOG" >> valid_found.txt
  fi
done < "$L"
echo "ALL_DONE $(date +%T)" >> progress.txt
