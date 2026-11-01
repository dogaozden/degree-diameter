#!/bin/bash
# scanmeta.sh d D LIST SECS: hmeta short random starts (2 seeds) on every group "N m k r fpf" of LIST, smallest N first
cd "$(dirname "$0")"; d=$1; D=$2; L=$3; sec=${4:-20}
while read N m k r f; do for s in 1 2; do out=rec/sm_d${d}D${D}_${m}_${k}_$s
  res=$(env T0=8 T1=1 REHEAT=400 THREADS=1 timeout $((sec + 20)) ./hmeta $d $D $sec $s 16 $out $m $k $r 2>/dev/null | grep RESULT); echo "$N $m $k fpf=$f $res"
  case "$res" in *best=0\ *) echo FOUND $out; break;; esac; done; done < $L
