#!/bin/bash
# hq.sh: one director Haar job (haar_big0 search: haar_big plus f = 0), then haarcheck_gen on any find.
# usage: hq.sh d D secs seed K fam p n "k m f" [THREADS]      env: CTH (checker threads, 4), NOCHECK=1 (search only)
cd "$(dirname "$0")"
d=$1 D=$2 secs=$3 seed=$4 K=$5 fam=$6 p=$7 n=$8 orb=$9 th=${10:-2}
set -- $orb; tag=d${d}D${D}_${fam}_${p}_${n}_orb$1-$2-$3_s${seed}
ORBIT="$orb" THREADS=$th ./bin/haar_big0 $d $D $secs $seed $K runs/$tag.out $fam $p $n > runs/$tag.log 2>&1
grep RESULT runs/$tag.log | tail -1
if grep -q "best=0 " runs/$tag.log && [ -s runs/$tag.out ] && [ -z "$NOCHECK" ]; then ./gen.sh runs/$tag.out; fi
