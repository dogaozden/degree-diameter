#!/bin/bash
# usage: reanneal.sh ID I J SECS  -- re-export group SmallGroup(1080,ID) (SKIPHAAR), re-anneal pair I J, score the best graph
cd /home/user/degree-diameter/research/squads/s65r2/c5
d=rean_$1_$2_$3; mkdir -p $d
gap -q -c "ORDER:=1080; H_ORDER:=3; OUTDIR:=\"$d\"; IDS:=[$1]; SKIPHAAR:=true;" sg_export.g > $d/gap.log 2>&1
f=$d/sg1080_$1_$2_$3.dc2
SA=1 SECS=$4 SEED=2 timeout 1200 nice -n 10 ./dcenum $f 6 5 $d/best.edges > $d/out.txt 2>&1
tail -1 $d/out.txt
./score65 $d/best.edges
