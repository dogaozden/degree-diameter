#!/bin/bash
# Sequential haarex2 driver for c1 (card s65r3-c1). Usage: run_list.sh LISTFILE DEADLINE_EPOCH
cd /home/user/degree-diameter/research/squads/s65r3/c1
TOOLS=/home/user/degree-diameter/research/s65/tools
LIST=$1; DEADLINE=$2
tail -n +2 "$LIST" | while read id; do
  [ -z "$id" ] && continue
  now=$(date +%s)
  remain=$(( DEADLINE - now ))
  if [ "$remain" -lt 60 ]; then echo "STOP before $id (deadline)" >> driver.log; break; fi
  tmo=$(( remain < 420 ? remain : 420 ))
  ord=${id%_*}; sid=${id#*_}
  gap -q -c "K:=SmallGroup($ord,$sid);; FN:=\"hx_$id.txt\";;" $TOOLS/haarex2.g > exp_$id.out 2>&1
  struct=$(grep -o 'gens=[0-9]* .*' exp_$id.out | sed 's/^gens=[0-9]* //')
  [ -z "$struct" ] && struct="EXPORT_FAILED"
  if [ -f hx_$id.txt ]; then
    start=$(date +%s)
    timeout $tmo nice -n 10 $TOOLS/haarex2 hx_$id.txt > h$id.log 2>&1
    rc=$?
    el=$(( $(date +%s) - start ))
    npairs=$(grep -o 'pair classes=[0-9]*' h$id.log | head -1 | sed 's/pair classes=//')
    if grep -q '^DONE' h$id.log; then
      fin=yes; done_p=$npairs
      sets=$(grep '^DONE' h$id.log | sed 's/.*sets=\([0-9]*\).*/\1/')
      minA=$(grep '^DONE' h$id.log | sed 's/.*minA=\([0-9-]*\).*/\1/')
    else
      fin=no
      lastp=$(grep '^PAIR' h$id.log | tail -1 | awk '{print $2}')
      done_p=$(( ${lastp:-0} + 1 ))
      sets="-"; minA="-"
      # minA lower bound from partial PAIR lines
      pm=$(grep '^PAIR' h$id.log | sed 's/.*minA=\([0-9-]*\).*/\1/' | sort -n | head -1)
      [ -n "$pm" ] && minA="$pm(partial)"
    fi
    valid=$(grep -c '^VALID' h$id.log)
    bunc=$(grep '^ASIDE' h$id.log | sed 's/.*Bunc=\([0-9]*\).*/\1/' | sort -n | head -1)
    [ -z "$bunc" ] && bunc="-"
    echo "$id | $struct | $fin ($done_p/${npairs:-?}) | sets=$sets | valid=$valid | minA=$minA | minBunc=$bunc | rc=$rc t=${el}s" >> table.txt
    if [ "$valid" -gt 0 ]; then echo "!!! VALID in $id" >> driver.log; fi
    rm -f hx_$id.txt
  else
    echo "$id | $struct | EXPORT_FAILED | - | - | - | - | -" >> table.txt
  fi
  echo "done $id $(date +%T)" >> driver.log
done
echo "LOOP_END $(date +%T)" >> driver.log
