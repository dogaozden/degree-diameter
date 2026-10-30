#!/bin/bash
# run_c5.sh LIST: for each line "n id ..." (largest first): export SmallGroup(n,id) (table + ALPHA classes) and all
# automorphisms with GAP, run dsym (doubly symmetric Haar sets), verify the first hit with apsp, log one line per group.
D=/home/user/degree-diameter/research/squads/d75-r2/c5; R=/home/user/degree-diameter/research/d75-raise/src
T=$D/tmp; O=$D/out; mkdir -p $T $O/edges; export TMPDIR=$T
SUM=$O/summary.txt
while read n id rest; do
  [ -z "$n" ] && continue
  t0=$(date +%s)
  timeout 300 nice -n 15 gap -q -c "N:=$n;; ID:=$id;; OUT:=\"$T/g_${n}_${id}.ht\";;" $R/export.g > $T/gap_${n}_${id}.log 2>&1
  timeout 300 nice -n 15 gap -q -c "N:=$n;; ID:=$id;; OUT:=\"$T/a_${n}_${id}.txt\";;" $R/allaut.g > $T/gapa_${n}_${id}.log 2>&1
  if [ ! -s $T/g_${n}_${id}.ht ] || [ ! -s $T/a_${n}_${id}.txt ]; then echo "$n $id GAPFAIL" >> $SUM; continue; fi
  MAXSETS=${MAXSETS:-2000000} COSTSTRIDE=64 EDGDIR=$O/edges/${n}_${id} timeout 600 nice -n 15 $D/dsym $T/g_${n}_${id}.ht $T/a_${n}_${id}.txt > $O/${n}_${id}.out 2>&1
  rc=$?
  auts=$(head -1 $T/a_${n}_${id}.txt)
  hits=$(grep -c "^SOL" $O/${n}_${id}.out)
  bc=$(grep "^BESTCOST" $O/${n}_${id}.out | awk '{print $2}')
  pairs=$(grep -c "^PAIR" $O/${n}_${id}.out)
  capped=$(grep -c CAPPED $O/${n}_${id}.out)
  ver=NA
  if [ "$hits" -gt 0 ] && [ -s $O/edges/${n}_${id}/hit_0.edges ]; then
     ver=$($R/apsp $O/edges/${n}_${id}/hit_0.edges 7 5 | tail -1)
  fi
  echo "$n $id auts $auts pairs $pairs hits $hits bestcost ${bc:-NA} capped $capped rc $rc secs $(( $(date +%s) - t0 )) apsp[$ver]" >> $SUM
  rm -f $T/g_${n}_${id}.ht $T/a_${n}_${id}.txt
done < "$1"
echo ALLDONE >> $SUM
