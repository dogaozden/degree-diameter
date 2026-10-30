#!/bin/bash
# usage: basin/run.sh BASE GROUP TAG SEED0 NRUNS SECS   (vl short anneals; 2-opt of every cost<=2 result; 3-opt of cost 1)
base=$1; grp=$2; tag=$3; s0=$4; n=$5; secs=$6
out=basin/$tag; mkdir -p $out
for ((s=s0; s<s0+n; s++)); do
  sol=$out/s$s.sol
  D=5 SWAP=0.03 SECS=$secs SEED=$s OUT=$sol nice -n 5 ./vl $base $grp >/dev/null 2>&1
  c=$(grep -o "cost [0-9]*" $sol | awk '{print $2}')
  echo "seed $s cost $c" >> $out/log.txt
  if [ "$c" = "0" ]; then echo "HIT seed $s cost 0" >> $out/log.txt; cp $sol $out/HIT_s$s.sol; continue; fi
  if [ "$c" -le 2 ]; then
    k=2; [ "$c" -le 1 ] && k=3
    nice -n 5 ./kopt $sol $grp $k > $out/k_s$s.txt 2>/dev/null
    if grep -q SOL $out/k_s$s.txt; then echo "HIT seed $s kopt" >> $out/log.txt; else rm -f $out/k_s$s.txt; fi
  fi
  [ "$c" -gt 2 ] && rm -f $sol
done
