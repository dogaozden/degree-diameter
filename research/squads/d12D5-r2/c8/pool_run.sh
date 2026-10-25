#!/bin/bash
# usage: pool_run.sh POOLSEED SECS ANNSEED ; one run at m=78 over the variant pool v<POOLSEED>; if best_cost=0 build lift + apsp
D=/home/user/degree-diameter/research/squads/d12D5-r2/c8
R=/home/user/degree-diameter/research/d12D5
P=$1; SECS=$2; ANN=$3; OUT=$D/vr${P}_m78
cd $D
t0=$(date +%s)
WRITEBEST=1 VARLIST=$D/list${P}.txt DIAGBT=1 INIT_ECHART=$D/v${P}_0.echart timeout 1500 nice -n 10 $R/mlift_ejoint2 $R/base_k33m.txt $R/tables/z26.txt $SECS $ANN 2 0.9 $OUT > $OUT.log 2>&1
t1=$(date +%s)
BC=$(grep -o 'best_cost=[0-9]*' $OUT.log | cut -d= -f2)
echo "pool=$P secs=$SECS ann=$ANN m=78 best_cost=$BC wall=$((t1-t0))s" >> $D/pool_results.txt
if [ "$BC" = "0" ]; then
  python3 $R/elift.py $OUT.edges $OUT.echart $D/lift_m78_p${P}.edges >> $D/pool_results.txt 2>&1
  $R/apsp $D/lift_m78_p${P}.edges 12 5 > $D/apsp_m78_p${P}.txt 2>&1
  echo "apsp: $(cat $D/apsp_m78_p${P}.txt)" >> $D/pool_results.txt
fi
echo DONE >> $D/pool_results.txt
