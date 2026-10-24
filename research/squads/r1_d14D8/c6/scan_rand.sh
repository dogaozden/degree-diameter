#!/bin/bash
# usage: scan_rand.sh hmode seed m1 m2 ...
S=/home/user/degree-diameter/research/squads/cells/d14D8_work
D=/home/user/degree-diameter/research/squads/r1_d14D8/c6
hm=$1; sd=$2; shift 2
for m in "$@"; do
  f=$D/runs/rand_h${hm}_s${sd}_m${m}.txt
  timeout 900 nice -n 10 python3 $D/mk_c6.py 9 $m $sd 4 $hm $f >/dev/null 2>&1
  r=$(timeout 900 nice -n 10 $S/liftevalw $f 8 r:20:1 2>/dev/null)
  echo "m=$m hmode=$hm seed=$sd: $r"
  rm -f $f
done
