#!/bin/bash
# Exhaustive Haar graphs H(G, S), |S| = d, over every SmallGroup of order LO..HI with |G/G'| <= B, at diameter D.
# Usage: scanhaar_all.sh d D LO HI B OUT.tsv [LIMIT]
d=$1; D=$2; LO=$3; HI=$4; B=$5; OUT=$6; LIM=${7:-0}
T=$(cd "$(dirname "$0")" && pwd)
GDIR=${GDIR:-/tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/groups}/haar
mkdir -p $GDIR; BASE=$T/bases/dipole$d.txt
for N in $(seq $LO $HI); do
  case $N in 256|512|768|1024) echo "skip $N" >&2; continue;; esac
  echo "lo:=$N;; hi:=$N;; B:=$B;; dir:=\"$GDIR\";; Read(\"$T/gap_export_filt.g\");" | gap -q -o 12g > /dev/null 2>&1
  cat $GDIR/sum$N.txt >> $OUT.sum
  [ -s $GDIR/t$N.txt ] || { rm -f $GDIR/t$N.txt; continue; }
  python3 $T/split_groups.py $GDIR/t$N.txt $GDIR/b$N
  for r in $GDIR/b$N/*.reps; do
    b=${r%.reps}
    m=$($T/bin/genhaar $d < $r | LIMIT=$LIM ONLYLOW=1 $T/bin/flift $BASE $b.bin $d $D eval 2>&1 > $b.D$D.low | tail -1)
    echo -e "$N\t$(cut -d' ' -f2- $b.info)\t$m" >> $OUT
    [ -s $b.D$D.low ] && echo "HIT $b $(head -1 $b.D$D.low)" >> $OUT.hits
  done
  rm -rf $GDIR/b$N $GDIR/t$N.txt
done
echo DONE >> $OUT
