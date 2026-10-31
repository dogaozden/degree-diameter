#!/bin/bash
# sweep4.sh LIST DEADLINE_EPOCH: for each "N ID" line of LIST (smallest orders first): GAP export of the ALPHA 4
# classes (export4.g), anti4k6 o4 (types A, B; EXTRA=1 with CAP), one summary line in sweep.txt; a valid hit
# (XX = G) is checked with apsp and kept in hits/.  Stops when the deadline passes.
D=/home/user/degree-diameter/research/squads/sd5-r1/c1
APSP=/home/user/degree-diameter/research/selfdual-d5/src/apsp
mkdir -p $D/tmp $D/out $D/hits
while read n id; do
  [ $(date +%s) -ge $2 ] && break
  F=$D/tmp/g${n}_${id}.ht
  t0=$(date +%s)
  timeout 150 nice -n 15 gap -q -c "N:=$n;; ID:=$id;; OUT:=\"$F\";;" $D/export4.g > /dev/null 2>&1
  if [ ! -s $F ] || ! grep -q CENT $F; then echo "$n $id GAPFAIL secs $(( $(date +%s) - t0 ))" >> $D/sweep.txt; rm -f $F; continue; fi
  t1=$(date +%s)
  mkdir -p $D/hits/${n}_${id}
  EXTRA=1 CAP=300000 EDGEDIR=$D/hits/${n}_${id} timeout 300 nice -n 15 $D/anti4k6 $F o4 > $D/out/${n}_${id}.out 2>&1
  rc=$?
  dn=$(grep "^DONE" $D/out/${n}_${id}.out)
  sols=$(echo "$dn" | sed -n 's/.* sols \([0-9-]*\) .*/\1/p')
  best=$(echo "$dn" | sed -n 's/.* best \(-*[0-9]*\) bestrec.*/\1/p')
  v=""
  if [ "${sols:-0}" -gt 0 ]; then
    for e in $D/hits/${n}_${id}/sol*.edges; do [ -f "$e" ] && v="$v $(timeout 120 $APSP $e 6 5 | tail -1)"; done
    echo "HIT $n $id sols $sols apsp: $v" >> $D/hits/HITS.txt
  fi
  echo "$n $id ninv $(grep -o 'ninv [0-9]*' $F | head -1 | cut -d' ' -f2) ngap $(grep -c '^ALPHA 4' $F) rc $rc sols ${sols:-NA} best ${best:-NA} gapsecs $(( t1 - t0 )) secs $(( $(date +%s) - t1 )) apsp:${v:- none}" >> $D/sweep.txt
  rm -f $F
  rmdir $D/hits/${n}_${id} 2>/dev/null
done < $1
echo SWEEPDONE >> $D/sweep.txt
