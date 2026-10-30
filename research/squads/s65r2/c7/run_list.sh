#!/bin/bash
# usage: run_list.sh TL id1 id2 ...   (ids like 360_53)
cd /home/user/degree-diameter/research/squads/s65r2/c7
GT=/home/user/degree-diameter/research/s65/tools
TL=$1; shift
for id in "$@"; do
  ord=${id%_*}; num=${id#*_}
  fn=hx_${ord}_${num}.txt
  if [ ! -s "$fn" ]; then
    gap -q -c "K:=SmallGroup($ord,$num);; FN:=\"$fn\";;" $GT/haarex2.g > exp_${ord}_${num}.out 2>&1
  fi
  struct=$(grep -o 'EXPORTED.*' exp_${ord}_${num}.out | sed 's/.* gens=[0-9]* //')
  start=$(date +%T)
  timeout $TL nice -n 10 ./haarex2b "$fn" > h${ord}_${num}.log 2>&1
  rc=$?
  total=$(grep -o 'pair classes=[0-9]*' h${ord}_${num}.log | grep -o '[0-9]*$')
  if grep -q '^DONE' h${ord}_${num}.log; then
    d=$(grep '^DONE' h${ord}_${num}.log)
    sets=$(echo "$d" | grep -o 'sets=[0-9]*' | cut -d= -f2)
    valid=$(echo "$d" | grep -o 'valid=[0-9]*' | cut -d= -f2)
    minA=$(echo "$d" | grep -o 'minA=[0-9]*' | cut -d= -f2)
    fin="yes (${total}/${total} pairs)"
  else
    last=$(grep '^PAIR' h${ord}_${num}.log | tail -1 | awk '{print $2}')
    sets=$(grep '^PAIR' h${ord}_${num}.log | awk -F'sets=' '{split($2,a," "); s+=a[1]} END{print s}')
    valid=$(grep -c '^VALID' h${ord}_${num}.log)
    minA=$(grep '^PAIR' h${ord}_${num}.log | grep -o 'minA=[0-9]*' | cut -d= -f2 | sort -n | head -1)
    fin="no (last PAIR printed ${last:-none} of ${total}; rc=$rc)"
  fi
  bestline=$(grep '^BEST' h${ord}_${num}.log | tail -1)
  printf '%s | %s | finished %s | sets=%s | valid=%s | minA=%s | started %s | %s\n' "$id" "$struct" "$fin" "$sets" "$valid" "$minA" "$start" "$bestline" >> table.txt
  echo "DONE_ID $id rc=$rc $(date +%T)"
done
