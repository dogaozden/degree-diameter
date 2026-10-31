#!/bin/bash
# c1 deep run on the best screened groups: sdtabu2 SECS=30 on types f=1,3,5 (records as in screen).
cd /home/user/degree-diameter || exit 1
C1=/home/user/degree-diameter/research/squads/sd5b-r1/c1
export TMPDIR=$C1/tmp
for spec in "$@"; do
  base=$C1/ex/g_${spec}
  K=9 SECS=30 NB=96 STALL=2000 TYPES=1,3,5 NOID=1 SEED=7 ENDG=3 EDGES=$base.deep.edges \
    timeout 900 nice -n 15 research/selfdual-d5/src/sdtabu2 $base.ht all > $base.deep.out 2>&1
  best=$(grep '^TABU' $base.deep.out | sed -E 's/.*best ([0-9]+).*/\1/' | sort -n | head -1)
  echo "DEEP $spec best=${best:-NA} sols=$(grep '^TABU' $base.deep.out | sed -E 's/.*sols ([0-9]+).*/\1/' | sort -n | tail -1) t=$(date +%T)" >> $C1/deep.log
done
echo DEEPEND >> $C1/deep.log
