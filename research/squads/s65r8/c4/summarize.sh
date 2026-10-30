#!/bin/bash
# builds table.txt from driver.status and the h<ID>.log files
cd /home/user/degree-diameter/research/squads/s65r8/c4
LIST=/home/user/degree-diameter/research/s65/haar/r8_list_3.txt
: > table.txt
while read ID; do
  [ -z "$ID" ] && continue
  L=h${ID}.log
  STRUCT=$(grep -E "^EXPORT $ID ::" driver.status | sed -E 's/.*gens=[0-9]+ //')
  if [ -z "$STRUCT" ]; then STRUCT=$(grep -h "EXPORTED" driver.status | head -0); fi
  if [ ! -f "$L" ]; then echo "$ID | ${STRUCT:-?} | not reached | - | -" >> table.txt; continue; fi
  VAL=$(grep -c '^VALID' $L)
  if grep -q '^DONE' $L; then
    D=$(grep '^DONE' $L)
    P=$(echo "$D" | sed -E 's/.*pairs=([^ ]+).*/\1/')
    A=$(echo "$D" | sed -E 's/.*Acovered=([^ ]+).*/\1/')
    echo "$ID | ${STRUCT:-?} | pairs $P (done) | Acovered $A | valid $VAL" >> table.txt
  else
    LASTP=$(grep '^PAIR' $L | tail -1 | awk '{print $2}')
    ACV=$(grep '^PAIR' $L | grep -vc 'acovers=0')
    echo "$ID | ${STRUCT:-?} | pairs 0..${LASTP:-none} (PARTIAL, no DONE) | Acovered>0 seen in $ACV pair lines | valid $VAL" >> table.txt
  fi
done < $LIST
cat table.txt
