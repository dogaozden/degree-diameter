#!/bin/bash
# usage: sweep.sh F1 F2 seed "m list" SAMPLE
export OMP_NUM_THREADS=1
cd /home/user/degree-diameter/research/squads/r2_d8c/c3
G=/home/user/degree-diameter/research/squads/cells/d10D8_work/glift
PHI=/home/user/degree-diameter/research/squads/r1_d8c/c5/dual9.phi
F1=$1; F2=$2; S=$3; MS=$4; SAMP=${5:-r:64:1}
for m in $MS; do
  f=work/${F1}_${F2}_s${S}_m${m}.txt
  python3 -I gen3.py 9 $PHI $m $S $f $F1 $F2 2>/dev/null
  c=$(timeout 900 nice -n 10 $G $f $SAMP 2>/dev/null | grep COST | awk '{print $2}')
  echo "$F1 $F2 s$S m$m cost $c"
  rm -f $f
done
