#!/bin/bash
# usage: run_group.sh m k r NSLICES  -> runs exh_meta slices through flift eval (D=8), one process at a time
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r3/e01
m=$1; k=$2; r=$3; n=$4
for ((i=0;i<n;i++)); do
  THREADS=1 timeout 120 nice -n 10 bash -c "python3 $T/exh_meta.py $m $k $r --slice $i/$n | LIMIT=2 ONLYLOW=1 $T/flift $T/bases/dipole4.txt meta:$m:$k:$r 4 8 eval > $D/exh_${m}_${k}_${r}_s$i.low 2> $D/exh_${m}_${k}_${r}_s$i.err"
  echo "meta $m $k $r slice $i/$n rc=$? $(grep -i min $D/exh_${m}_${k}_${r}_s$i.err | tail -1) lowlines=$(wc -l < $D/exh_${m}_${k}_${r}_s$i.low)"
done
