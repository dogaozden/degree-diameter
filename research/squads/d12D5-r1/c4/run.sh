#!/bin/bash
# usage: run.sh M SEED T0 PV INIT   (M = 69 (Z_23) or 72 (Z_24); INIT = echart | chart)
# One mlift_ejoint run (150 s CPU, timeout 400), then elift + apsp if best_cost <= 6. Appends a line to c4/runs.txt.
M=$1; SEED=$2; T0=$3; PV=$4; INIT=$5
D=/home/user/degree-diameter/research/squads/d12D5-r1/c4
R=/home/user/degree-diameter/research/d12D5
case $M in
  69) TAB=$R/tables/z23.txt ;;
  72) TAB=$R/tables/z24.txt ;;
  *) echo "bad M"; exit 1 ;;
esac
TAG=m${M}_s${SEED}_T${T0}_P${PV}_${INIT}
OUT=$D/runs/$TAG
if [ "$INIT" = echart ]; then
  VAR=INIT_ECHART; INITV=$R/graphs/d12D5_n10692_k33m_z22e_echart.txt
else
  VAR=INIT_CHART; INITV=$R/graphs/d12D5_n9720_k33m_z20_chart.txt
fi
START=$(date +%H:%M:%S)
env THREADS=1 WRITEBEST=1 $VAR=$INITV timeout 400 nice -n 10 $R/mlift_ejoint $R/base_k33m.txt $TAB 150 $SEED $T0 $PV $OUT > $OUT.log 2>&1
RC=$?
COST=$(grep -o 'best_cost=[0-9]*' $OUT.log | head -1 | cut -d= -f2)
[ -z "$COST" ] && COST=NA
VERDICT=n/a
if [ "$COST" != NA ] && [ "$COST" -le 6 ]; then
  if python3 $R/elift.py $OUT.edges $OUT.echart $D/lift_$TAG.edges > $OUT.elift 2>&1; then
    timeout 300 nice -n 10 $R/apsp $D/lift_$TAG.edges 12 5 > $OUT.apsp 2>&1
    if grep -q 'RESULT VALID' $OUT.apsp; then VERDICT=VALID; else VERDICT=INVALID; fi
  else
    VERDICT=elift-failed
  fi
  rm -f $D/lift_$TAG.edges
fi
echo "$TAG m=$M seed=$SEED T0=$T0 PV=$PV init=$INIT start=$START rc=$RC best_cost=$COST apsp=$VERDICT" >> $D/runs.txt
echo "$TAG start=$START rc=$RC best_cost=$COST apsp=$VERDICT"
grep 'best_cost' $OUT.log | head -2
