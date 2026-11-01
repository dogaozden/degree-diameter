#!/bin/bash
# hq.sh: one director Haar job: search with haar_big, then an independent check of any find.
# usage: hq.sh d D secs seed K fam p n "ORBIT" [THREADS]
# A find is copied to ../sols/ only if the independent checker says VALID (hcheckpsl for PSL, hcheck5 for SL).
cd "$(dirname "$0")"
d=$1 D=$2 secs=$3 seed=$4 K=$5 fam=$6 p=$7 n=$8 orb=$9 th=${10:-2}
tag=d${d}D${D}_${fam}_${p}_${n}_orb3_s${seed}
ORBIT="$orb" THREADS=$th ./bin/haar_big $d $D $secs $seed $K runs/$tag.out $fam $p $n > runs/$tag.log 2>&1
grep RESULT runs/$tag.log | tail -1
if grep -q "best=0 " runs/$tag.log && [ -s runs/$tag.out ]; then
  if [ $fam = psl ]; then chk=hcheckpsl; else chk=hcheck5; fi
  THREADS=$th ../../bighaar/check_one.sh $chk runs/check_${chk}_$tag.txt ./bin/$chk runs/$tag.out
  grep -h -E "VALID|ecc" runs/check_${chk}_$tag.txt | tail -2
  if grep -q "^VALID" runs/check_${chk}_$tag.txt; then cp runs/$tag.out ../sols/$tag.txt; echo "saved ../sols/$tag.txt"; fi
fi
