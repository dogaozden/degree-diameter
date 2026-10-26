#!/bin/bash
# meta_screen.sh d LO HI SECONDS SEEDS OUTLOG [STRIDE OFFSET]: haar5 anneal on every metacyclic-type group (metacyclic_ids.txt)
# with LO <= order <= HI; STRIDE/OFFSET split the list between workers.
T=$(dirname $0); d=$1; st=${7:-1}; of=${8:-0}; mkdir -p $T/../tables/meta
awk -v lo=$2 -v hi=$3 '!/^#/ && $1>=lo && $1<=hi {print $1, $2}' $T/../metacyclic_ids.txt | awk -v s=$st -v o=$of 'NR%s==o' | while read n i; do
  f=$T/../tables/meta/g${n}_$i.bin
  [ -f $f ] || python3 $T/gapgroup.py table $n $i $f
  for ((s=1; s<=$5; s++)); do
    r=$(timeout $(( $4 + 30 )) $T/haar5 anneal $f $d $4 $s 2>/dev/null | tail -1)
    echo "$n $i seed=$s :: $r" >> $6
  done
done
echo DONE >> $6
