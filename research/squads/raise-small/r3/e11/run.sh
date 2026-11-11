#!/bin/bash
# usage: run.sh P SPECS START END SEED SECS   (lines START..END of SPECS: "N m k r c d fpf")
T=/home/user/degree-diameter/research/frontier/raise_small
E=/home/user/degree-diameter/research/squads/raise-small/r3/e11
P=$1; SPECS=$2; S=$3; EN=$4; SEED=$5; SECS=$6
cd $E
sed -n "${S},${EN}p" $SPECS | while read N m k r c d fpf; do
  tab=tabs/g_${N}_${m}_${k}_${r}_x${c}.tab
  [ -f $tab ] || timeout 60 nice -n 10 python3 $T/tools/gtab.py $tab $m $k $r $c 2>/dev/null
  out=runs/p${P}_${N}_${m}_${k}_${r}_x${c}_s${SEED}.sol
  t0=$(date +%s)
  res=$(D=10 timeout 100 nice -n 10 $T/bin/salift_s $P $tab 1 $SEED $SECS 10 0.3 $out 2>/dev/null | grep 'end best' | tail -1)
  t1=$(date +%s)
  echo "p=$P N=$N m=$m k=$k r=$r c=$c d=$d fpf=$fpf seed=$SEED secs=$SECS wall=$((t1-t0)) :: ${res:-NORESULT}" >> results.log
done
