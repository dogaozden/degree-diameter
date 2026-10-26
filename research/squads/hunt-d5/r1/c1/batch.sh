#!/bin/bash
# Card c1: (9,5) orbit-symmetric Haar anneals, ORBIT="3 3 0", groups of order 1392 (centre-ascending), aut3 with nfix<=40.
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/c1
export OMP_NUM_THREADS=1 THREADS=1
DEADLINE=$(date -d "13:54:00" +%s)
: > batch.txt
awk '$3=="false"{print $5, $4, $2}' list_1392.txt | sort -k1,1n -k2,2nr | awk '{print $3}' | while read I; do
  [ "$(date +%s)" -lt "$DEADLINE" ] || break
  B=tab/g1392_${I}.bin
  [ -f "$B" ] || timeout 200 nice -n 10 python3 ../../tools/gapgroup.py table 1392 $I $B 3 >/dev/null 2>&1
  [ -f "$B.aut3" ] || { rm -f "$B"; continue; }
  NF=$(awk '{print $1}' "$B.aut3" | head -1)
  NONE=1
  j=0
  while read nf rest; do
    if [ "$nf" -le 40 ] && [ "$(date +%s)" -lt "$DEADLINE" ]; then
      R=$(AUT=$B.aut3 ALINE=$j ORBIT="3 3 0" timeout 60 nice -n 10 ../../tools/haar5 anneal $B 9 10 1 2>/dev/null | grep RESULT)
      echo "I=$I aline=$j nfix=$nf | $R" >> batch.txt
      NONE=0
    fi
    j=$((j+1))
  done < "$B.aut3"
  [ $NONE -eq 1 ] && echo "I=$I minnfix=$NF (none <=40)" >> batch.txt
  [ $NONE -eq 1 ] && rm -f "$B" "$B.aut3"
done
echo BATCH_DONE >> batch.txt
