#!/bin/bash
# hq.sh: one director haar_big0 search (job raise-d10); checks are run separately (chk.sh) so that big searches and
# big checks never overlap in memory.
# usage: hq.sh d D secs seed K fam p n "k m f" [THREADS] [TAGEXTRA]   (other env vars, e.g. FIXF=1 BOUNDCUR=1, pass through)
cd "$(dirname "$0")"
d=$1 D=$2 secs=$3 seed=$4 K=$5 fam=$6 p=$7 n=$8 orb=$9 th=${10:-2} tx=${11:-}
set -- $orb; tag=d${d}D${D}_${fam}_${p}_${n}_orb$1-$2-$3${tx}_s${seed}
echo "$(date -u +%T) start $tag env: FIXF=$FIXF BOUNDCUR=$BOUNDCUR TMAX=$TMAX TMIN=$TMIN START=$START" >> runs/hq.log
ORBIT="$orb" THREADS=$th ./bin/${HB:-haar_big0} $d $D $secs $seed $K runs/$tag.out $fam $p $n > runs/$tag.log 2>&1
r=$(grep RESULT runs/$tag.log | tail -1); echo "$(date -u +%T) end $tag: $r" >> runs/hq.log; echo "$r"
