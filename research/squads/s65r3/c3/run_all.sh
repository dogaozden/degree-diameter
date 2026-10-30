#!/bin/bash
# sequential exhaustive haarex2 runs over list_r3_2.txt (card c3, round s65r3)
C3=/home/user/degree-diameter/research/squads/s65r3/c3
TOOLS=/home/user/degree-diameter/research/s65/tools
DEADLINE=$(date -u -d "2026-10-30 08:34:30" +%s)
cd "$C3"
for id in $(grep -v '^360_71$' /home/user/degree-diameter/research/s65/haar/list_r3_2.txt); do
  now=$(date +%s); rem=$(( DEADLINE - now ))
  if [ $rem -lt 60 ]; then echo "STOP deadline before $id" >> run_all.out; break; fi
  to=$(( rem < 1200 ? rem : 1200 ))
  order=${id%_*}; num=${id#*_}
  gap -q -c "K:=SmallGroup($order,$num);; FN:=\"hx_$id.txt\";;" $TOOLS/haarex2.g > exp_$id.out 2>&1
  if [ ! -s hx_$id.txt ]; then echo "$id | EXPORT FAILED | no | - | - | - | -" >> table.txt; rm -f hx_$id.txt; continue; fi
  struct=$(grep EXPORTED exp_$id.out | sed 's/.*gens=[0-9]* //')
  start=$(date +%s)
  timeout $to nice -n 10 $TOOLS/haarex2 hx_$id.txt > h$id.log 2>&1
  rc=$?
  echo "$id rc=$rc secs=$(( $(date +%s) - start ))" >> run_all.out
  rm -f hx_$id.txt
  total=$(grep -o 'pair classes=[0-9]*' h$id.log | head -1 | cut -d= -f2)
  if grep -q '^DONE' h$id.log; then
    fin=yes; done_p=$total
    line=$(grep '^DONE' h$id.log)
    sets=$(echo "$line" | grep -o 'sets=[0-9]*' | cut -d= -f2)
    valid=$(echo "$line" | grep -o 'valid=[0-9]*' | cut -d= -f2)
    mina=$(echo "$line" | grep -o 'minA=[0-9]*' | cut -d= -f2)
  else
    fin=no
    last=$(grep '^PAIR' h$id.log | tail -1 | awk '{print $2}')
    done_p=$(( ${last:--1} + 1 ))
    sets=$(grep '^PAIR' h$id.log | grep -o 'sets=[0-9]*' | cut -d= -f2 | awk '{s+=$1} END{print s+0}')
    valid=$(grep -c '^VALID' h$id.log)
    mina=$(grep '^PAIR' h$id.log | grep -o 'minA=[0-9]*' | cut -d= -f2 | sort -n | head -1)
  fi
  bunc=$(grep '^ASIDE' h$id.log | grep -o 'Bunc=[0-9]*' | cut -d= -f2 | sort -n | head -1)
  [ -z "$bunc" ] && bunc="-"
  [ -z "$sets" ] && sets=0
  [ -z "$mina" ] && mina="-"
  echo "$id | $struct | $fin ($done_p/$total) | $sets | $valid | $mina | $bunc" >> table.txt
  if [ "${valid:-0}" -gt 0 ]; then grep '^VALID' h$id.log > VALID_$id.txt; echo "!!! VALID in $id" >> run_all.out; fi
done
echo ALLDONE >> run_all.out
