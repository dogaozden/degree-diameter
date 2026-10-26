#!/bin/bash
# Stabiliser-2 bi-coset graphs over every SmallGroup of order LO..HI (n = |G|) with |G/G'| <= 2D, diameter D.
# Usage: scan_bicoset.sh D LO HI OUT.tsv
D=$1; LO=$2; HI=$3; OUT=$4; B=$((2*D))
T=$(cd "$(dirname "$0")" && pwd)
GDIR=${GDIR:-/tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/groups}/bc$D
mkdir -p $GDIR
for N in $(seq $LO $HI); do
  [ $((N % 2)) = 1 ] && continue
  case $N in 256|512|768|1024|1536|2048) echo "skip $N" >&2; continue;; esac
  echo "lo:=$N;; hi:=$N;; B:=$B;; dir:=\"$GDIR\";; Read(\"$T/gap_export_bicoset.g\");" | gap -q -o 12g > /dev/null 2>&1
  cat $GDIR/sum$N.txt >> $OUT.sum
  [ -s $GDIR/t$N.txt ] || { rm -f $GDIR/t$N.txt; continue; }
  python3 $T/split_groups.py $GDIR/t$N.txt $GDIR/b$N
  for r in $GDIR/b$N/*.reps; do
    b=${r%.reps}
    cut -d' ' -f2- $r > $b.inv
    res=$($T/bin/bicoset $b.bin $D $b.inv 3)
    echo -e "$N\t$(cut -d' ' -f2- $b.info)\t$(echo "$res" | grep BEST)" >> $OUT
    echo "$res" | grep HIT | sed "s#^#$N $(cut -d' ' -f2 $b.info) #" >> $OUT.hits
  done
  rm -rf $GDIR/b$N $GDIR/t$N.txt
done
echo DONE >> $OUT
