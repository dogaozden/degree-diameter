#!/bin/bash
# Exhaustive 2+2 cubic lifts over EVERY SmallGroup of orders LO..HI at diameter D (Aut-reduced, b<c).
# Usage: scan22f.sh LO HI D OUT.tsv [LIMIT] [B]  (only groups with |G/G'| <= B; the rest fail by the quotient bound)   (groups exported to $GDIR; minima above LIMIT are lower bounds)
LO=$1; HI=$2; D=$3; OUT=$4; LIM=${5:-0}; B=${6:-124}
T=$(cd "$(dirname "$0")" && pwd)
GDIR=${GDIR:-/tmp/claude-0/-home-user-degree-diameter/6bbfb942-4016-5a09-834c-7684c0cc81b5/scratchpad/groups}/f22
mkdir -p $GDIR
for N in $(seq $LO $HI); do
  [ "$N" = 256 ] && { echo "skip 256" >&2; continue; }
  if [ ! -f $GDIR/t$N.txt ]; then
    echo "lo:=$N;; hi:=$N;; B:=$B;; dir:=\"$GDIR\";; Read(\"$T/gap_export_filt.g\");" | gap -q -o 8g > /dev/null 2>&1
  fi
  cat $GDIR/sum$N.txt >> $OUT.sum; [ -s $GDIR/t$N.txt ] || continue
  python3 $T/split_groups.py $GDIR/t$N.txt $GDIR/b$N
  for r in $GDIR/b$N/*.reps; do
    b=${r%.reps}
    m=$($T/bin/gen22 < $r | LIMIT=$LIM ONLYLOW=1 $T/bin/flift $T/bases/cubic/b22_cubic.txt $b.bin 3 $D eval 2>&1 > $b.D$D.low | tail -1)
    echo -e "$N\t$(cut -d' ' -f2- $b.info)\t$m" >> $OUT
    [ -s $b.D$D.low ] && echo "HIT $b $(head -1 $b.D$D.low)" >> $OUT.hits
  done
  rm -rf $GDIR/b$N $GDIR/t$N.txt
done
echo DONE >> $OUT
