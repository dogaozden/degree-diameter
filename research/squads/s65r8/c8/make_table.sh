#!/bin/bash
# one line per group: order_id | structure | pairs covered | Acovered | valid
cd /home/user/degree-diameter/research/squads/s65r8/c8
echo "order_id | structure | pairs covered | Acovered | valid"
while read ID; do
  [ -z "$ID" ] && continue
  O=${ID%_*}; G=${ID#*_}
  S=$(sed -n "s/^EXPORTED .* |Aut|=[0-9]* gens=[0-9]* //p" structure_${O}_${G}.txt 2>/dev/null)
  L=h${O}_${G}.log
  if [ -f "$L" ] && grep -q '^DONE' "$L"; then
    D=$(grep '^DONE' "$L" | tail -1)
    P=$(echo "$D" | sed -n 's/.*pairs=\([^ ]*\).*/\1/p')
    A=$(echo "$D" | sed -n 's/.*Acovered=\([^ ]*\).*/\1/p')
    V=$(echo "$D" | sed -n 's/.*valid=\([^ ]*\).*/\1/p')
    echo "$ID | ${S:-?} | $P | $A | $V"
  elif [ -f "$L" ]; then
    LP=$(grep '^PAIR' "$L" | tail -1 | awk '{print $2}')
    AC=$(grep -c 'acovers=[1-9]\|ASIDE' "$L")
    echo "$ID | ${S:-?} | partial, last PAIR ${LP:-none} (timeout/not reached) | ASIDE-lines=$AC | ? "
  else
    echo "$ID | ${S:-?} | not reached | - | -"
  fi
done < /home/user/degree-diameter/research/s65/haar/r8_list_7.txt
