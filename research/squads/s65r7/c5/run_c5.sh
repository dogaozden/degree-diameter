#!/bin/bash
# c5: sequential exhaustive haarex3 over hi_list_4 (one process at a time). Start limit 30 min, hard end 35 min.
cd /home/user/degree-diameter/research/squads/s65r7/c5 || exit 1
TOOLS=/home/user/degree-diameter/research/s65/tools
LIST=/home/user/degree-diameter/research/s65/haar/hi_list_4.txt
T0=$(date +%s)
START_LIMIT=$((T0+1800))
END_LIMIT=$((T0+2100))
export THREADS=1
echo "START $(date +%T)" >> run.log
for id in $(cat "$LIST"); do
  ORDER=${id%_*}; ID=${id#*_}
  now=$(date +%s)
  if [ "$now" -ge "$START_LIMIT" ]; then echo "STOP before $id: 30-min start limit reached" >> run.log; break; fi
  tleft=$((END_LIMIT-now)); tmo=600; [ "$tleft" -lt "$tmo" ] && tmo=$tleft
  echo "=== $id start $(date +%T) timeout ${tmo}s" >> run.log
  timeout 120 gap -q -c "K:=SmallGroup($ORDER,$ID);; FN:=\"hx_${id}.txt\";;" $TOOLS/haarex2.g > exp_${id}.out 2>&1
  STRUCT=$(grep EXPORTED exp_${id}.out | sed -n 's/.*gens=[0-9]* //p')
  if [ ! -s hx_${id}.txt ]; then
    echo "$id | ${STRUCT:-export failed} | export failed | - | -" >> table.txt
    echo "export failed $id" >> run.log; continue
  fi
  timeout "$tmo" nice -n 10 $TOOLS/haarex3 hx_${id}.txt > h${id}.log 2>&1
  rc=$?
  K=$(grep -m1 '^N=' h${id}.log | sed -n 's/.*pair classes=\([0-9]*\).*/\1/p')
  ACOV=$(grep '^PAIR' h${id}.log | sed 's/.*acovers=//' | awk '{s+=$1} END{print s+0}')
  NVALID=$(grep -c '^VALID' h${id}.log)
  if grep -q '^DONE' h${id}.log; then
    MINA=$(grep '^DONE' h${id}.log | sed -n 's/.*minA=\(-*[0-9]*\).*/\1/p')
    DONEACOV=$(grep '^DONE' h${id}.log | sed -n 's/.*Acovered=\([0-9]*\).*/\1/p')
    COV="0..$((K-1)) of $K (complete, minA=$MINA)"; ACOV=$DONEACOV
    STATE=complete
  else
    LASTP=$(grep '^PAIR' h${id}.log | tail -1 | awk '{print $2}')
    COV="0..${LASTP:-none} of ${K:-?} (partial, rc=$rc)"
    STATE=partial
  fi
  echo "$id | ${STRUCT:-?} | $COV | $ACOV | $NVALID" >> table.txt
  echo "done $id state=$STATE cov=$COV acov=$ACOV valid=$NVALID rc=$rc $(date +%T)" >> run.log
  if [ "$NVALID" -gt 0 ]; then
    echo "!!! RECORD CANDIDATE $id: $NVALID VALID sets, see valid_${id}.txt and valid_export_${id}.txt" >> run.log
    grep '^VALID' h${id}.log > valid_${id}.txt
    mv hx_${id}.txt valid_export_${id}.txt
  else
    rm -f hx_${id}.txt
  fi
done
echo "ALLDONE $(date +%T)" >> run.log
