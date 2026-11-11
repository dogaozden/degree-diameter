#!/bin/bash
A=../../../squads/beyond-small/bin/apsp
for spec in "pg 16 17 3" "pg 17 18 3" "pg 19 20 3" "w 16 17 4" "w 17 18 4" "w 19 20 4"; do
  set -- $spec; k=$1; q=$2; d=$3; D=$4
  f=d${d}D${D}_${k}${q}.edges
  nice -n 5 python3 build_moore_d34.py $k $q $f > build_${k}${q}.log 2>&1
  { echo "builder: research/frontier/beyond/moore/build_moore_d34.py $k $q (job beyond-small, $(date -u +%FT%TZ))";
    echo "edge list sha256 (uncompressed): $(sha256sum $f | cut -c1-64)";
    $A $f $d $D; } > check_${f%.edges}.apsp.txt
done
echo ALLDONE > run_all.done
