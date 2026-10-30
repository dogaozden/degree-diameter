#!/bin/bash
# c2 driver2: h=4 orders 732 and 740 with the locally fixed exporter (coordinator's dc2_lib.g has a GAP syntax error)
C=/home/user/degree-diameter/research/beyond-haar-d5/coset
W=/home/user/degree-diameter/research/squads/bh5-r3/c2
P=$W/progress.txt
cd $C
for o in 740 732; do
  echo "START2 $o 4 $(date +%T)" >> $P
  dir=$W/tmp_${o}_4; mkdir -p $dir
  timeout 150 nice -n 10 gap -q -c "ORDER:=$o; H_ORDER:=4; OUTDIR:=\"$dir\";" $W/sg_export_fixed.g > $dir/gap.log 2>&1
  for f in $dir/*.dc2; do
    [ -e "$f" ] || continue
    r=$(timeout 200 nice -n 10 ./dcenum $f 5 5 ${f%.dc2}.edges 2000000 2>/dev/null | tail -1)
    echo "$r" >> $W/c2_results_h4.txt
    rm -f $f
  done
  echo "END2 $o rc=$? $(date +%T)" >> $P
done
echo ALLDONE2 $(date +%T) >> $P
