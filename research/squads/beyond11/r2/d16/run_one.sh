#!/bin/bash
# usage: run_one.sh arm(plain|center) d D p n ORBIT seed secs   (plain = bin/haar_big0; center = haar_big0_center with CENTER=1)
arm=$1; d=$2; DD=$3; p=$4; n=$5; orb=$6; seed=$7; secs=$8
D16=/home/user/degree-diameter/research/squads/beyond11/r2/d16
out=$D16/runs/d${d}D${DD}_sl_${p}_${n}_o${orb// /-}_${arm}_s${seed}.out
if [ "$arm" = center3 ]; then CENTER=3 ORBIT="$orb" THREADS=1 timeout 105 nice -n 10 $D16/haar_big0_center $d $DD $secs $seed 8 $out sl $p $n > $out.log 2>&1; elif [ "$arm" = center ]; then
  CENTER=1 ORBIT="$orb" THREADS=1 timeout 105 nice -n 10 $D16/haar_big0_center $d $DD $secs $seed 8 $out sl $p $n > $out.log 2>&1
else
  ORBIT="$orb" THREADS=1 timeout 105 nice -n 10 /home/user/degree-diameter/research/frontier/beyond11/bin/haar_big0 $d $DD $secs $seed 8 $out sl $p $n > $out.log 2>&1
fi
echo "$arm d=$d D=$DD sl p=$p n=$n seed=$seed: $(grep -h RESULT $out.log | cut -c1-200)"
