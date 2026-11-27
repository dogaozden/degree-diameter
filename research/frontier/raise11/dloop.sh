#!/bin/bash
# dloop.sh d fam p n "k m f" secs seed0 nseeds: fresh haar_big0 runs (THREADS=1) with seeds seed0.., each limited to
# secs seconds, until one solves (best=0, solution written).  Logs runs/<tag>_s<seed>.log; prints the solving tag.
cd "$(dirname "$0")"
d=$1 fam=$2 p=$3 n=$4 orb=$5 secs=$6 s0=$7 ns=$8
set -- $orb
for ((s = s0; s < s0 + ns; s++)); do
  tag=d${d}D11_${fam}_${p}_${n}_orb$1-$2-$3_s$s
  ORBIT="$orb" THREADS=1 ./bin/haar_big0 $d 11 $secs $s 4 runs/$tag.out $fam $p $n > runs/$tag.log 2>&1
  if grep -q "^wrote" runs/$tag.log; then echo "SOLVED $tag"; exit 0; fi
done
echo "NO SOLVE d=$d $fam $p $n seeds $s0..$((s0 + ns - 1))"
