#!/bin/bash
# sequential exhaustive haarex2 over the remaining list groups; no new group starts after 08:33 UTC
cd /home/user/degree-diameter/research/squads/s65r3/c4
TOOLS=/home/user/degree-diameter/research/s65/tools
DEADLINE=$(date -d "08:33" +%s)
for id in 360_90 360_110 352_10 352_17 352_21 352_25 352_42 352_54 352_59 352_82 352_100 352_154 354_1 360_93 360_113; do
  now=$(date +%s); rem=$((DEADLINE-now))
  if [ $rem -lt 90 ]; then echo "STOP before $id at $(date +%T)" >> run_rest.out; break; fi
  to=$(( rem < 1200 ? rem : 1200 ))
  ord=${id%_*}; grp=${id#*_}
  echo "START $id at $(date +%T) timeout $to" >> run_rest.out
  gap -q -c "K:=SmallGroup($ord,$grp);; FN:=\"hx_$id.txt\";;" $TOOLS/haarex2.g > exp_$id.out 2>&1
  struct=$(grep EXPORTED exp_$id.out | sed 's/.*gens=[0-9]* //')
  timeout $to nice -n 10 $TOOLS/haarex2 hx_$id.txt > h$id.log 2>&1; echo "EXIT $?" >> h$id.log
  rm -f hx_$id.txt
  python3 parse.py $id "$struct" >> table.txt
  grep -h -E "^VALID" h$id.log | sed "s/^/$id /" >> valid_found.txt
  echo "END $id at $(date +%T) $(tail -1 table.txt)" >> run_rest.out
done
echo "ALLDONE $(date +%T)" >> run_rest.out
