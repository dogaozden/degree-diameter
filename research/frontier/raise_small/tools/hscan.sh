#!/bin/bash
# hscan.sh D LIST SEEDS SECS OUTDIR: fresh-seed hmeta (degree 4) runs over every group "N m k r ..." of LIST;
# stops at the first cost 0 and checks it with metacheck.py. Log OUTDIR/log.txt.
H=$(cd "$(dirname "$0")/.." && pwd); D=$1; L=$2; SEEDS=$3; S=$4; O=$5; mkdir -p "$O"
while read N m k r rest; do
  for s in $SEEDS; do
    out=$O/s_${m}_${k}_${r}_$s
    res=$(THREADS=1 T0=8 T1=1 REHEAT=400 timeout $((6 * S + 120)) "$H/bin/hmeta" 4 $D $S $s 16 $out $m $k $r 2>/dev/null | grep RESULT)
    echo "N=$N m=$m k=$k r=$r seed=$s $res" | cut -c1-200 >> "$O/log.txt"
    if grep -q "best=0 " <<< "$res"; then python3 "$H/tools/metacheck.py" $out >> "$O/log.txt" 2>&1; exit 0; fi
  done
done < "$L"
