#!/bin/bash
# c1 pipeline: export each candidate (split records only) and screen with sdtabu2 (K=9, types f=1,3,5).
cd /home/user/degree-diameter || exit 1
C1=/home/user/degree-diameter/research/squads/sd5b-r1/c1
export TMPDIR=$C1/tmp
while read N ID p d z inv; do
  base=$C1/ex/g_${N}_${ID}
  timeout 300 nice -n 15 gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$base.ht\";; NOEXT:=1;;" research/selfdual-d5/src/export_sd.g > $base.gap.log 2>&1
  if [ ! -s $base.ht ]; then echo "EXPORTFAIL $N $ID" >> $C1/pipe.log; continue; fi
  K=9 SECS=2 NB=48 STALL=1000 TYPES=1,3,5 NOID=1 SEED=1 EDGES=$base.edges \
    timeout 400 nice -n 15 research/selfdual-d5/src/sdtabu2 $base.ht all > $base.out 2>&1
  best=$(grep '^TABU' $base.out | sed -E 's/.*best ([0-9]+).*/\1/' | sort -n | head -1)
  echo "DONE N=$N ID=$ID z=$z inv=$inv d=$d p=$p best=${best:-NA} recs=$(grep -c '^TABU' $base.out) t=$(date +%T)" >> $C1/pipe.log
  if [ "$best" = "0" ]; then echo "ZERO $N $ID" >> $C1/pipe.log; fi
done < $C1/cands.txt
echo PIPEEND >> $C1/pipe.log
