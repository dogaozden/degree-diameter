#!/bin/bash
# card c6: sequential exhaustive haarex3 over r8_list_5.txt, 30-min start cutoff, 35-min hard box.
W=/home/user/degree-diameter/research/squads/s65r8/c6
T=/home/user/degree-diameter/research/s65/tools
L=/home/user/degree-diameter/research/s65/haar/r8_list_5.txt
START=$(date +%s)
DEADLINE=$((START+2100))
cd "$W" || exit 1
: > table.txt
for id in $(cat "$L"); do
  ord=${id%_*}; num=${id#*_}
  now=$(date +%s)
  if [ $((now-START)) -gt 1800 ]; then
    echo "$id | not reached (30-min start cutoff) | - | - | -" >> table.txt; continue
  fi
  left=$((DEADLINE-now)); to=600; [ $left -lt 600 ] && to=$left
  gap -q -c "K:=SmallGroup($ord,$num);; FN:=\"hx_${ord}_${num}.txt\";;" $T/haarex2.g > exp_${ord}_${num}.out 2>&1
  struct=$(grep EXPORTED exp_${ord}_${num}.out | sed 's/.*gens=[0-9]* //')
  [ -z "$struct" ] && struct="EXPORT FAILED"
  t0=$(date +%s)
  timeout $to nice -n 10 $T/haarex3 hx_${ord}_${num}.txt > h${ord}_${num}.log 2>&1
  rc=$?
  t1=$(date +%s)
  rm -f hx_${ord}_${num}.txt exp_${ord}_${num}.out
  P=$(grep -o 'pair classes=[0-9]*' h${ord}_${num}.log | head -1 | cut -d= -f2)
  D=$(grep '^DONE' h${ord}_${num}.log)
  nvalid=$(grep -c '^VALID' h${ord}_${num}.log)
  nasum=$(grep '^PAIR' h${ord}_${num}.log | sed 's/.*acovers=//' | awk '{s+=$1} END{print s+0}')
  lastpair=$(grep '^PAIR' h${ord}_${num}.log | tail -1 | awk '{print $2}')
  if [ -n "$D" ]; then
    cov="0..$((P-1)) of $P (DONE)"
    acov=$(echo "$D" | sed 's/.*Acovered=\([0-9-]*\).*/\1/')
    val=$(echo "$D" | sed 's/.*valid=\([0-9-]*\).*/\1/')
  else
    cov="0..${lastpair:-none} of $P (TIMEOUT rc=$rc)"
    acov="$nasum+ (partial)"
    val="$nvalid (partial)"
  fi
  echo "$id | $struct | $cov | $acov | $val | wall $((t1-t0))s" >> table.txt
  if [ "$nvalid" -gt 0 ]; then echo "$id" >> VALID_FOUND.txt; grep '^VALID' h${ord}_${num}.log >> VALID_FOUND.txt; fi
done
echo "ALLDONE $(date +%s)" >> table.txt
