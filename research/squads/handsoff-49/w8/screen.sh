#!/bin/bash
# screen.sh SECS SEED IDX... : run wl on groups/gNN.bin for each index, one at a time; summary to screen.txt
S=$1; SEED=$2; shift 2
for i in "$@"; do
  f=$(printf "groups/g%02d.bin" $i)
  r=$(nice -n 10 ./wl ../seeds/d4D5_162.edges $f 9 $S $SEED runs/scr_g$i 2>/dev/null | grep RESULT | head -1)
  echo "g$i $(head -c 0 /dev/null)$(python3 ../../tools/groups.py "$(sed -n "${i}p" groups/specs.txt)" 2>/dev/null | head -1 | cut -d' ' -f1) [$(sed -n "${i}p" groups/specs.txt)] $r" >> screen.txt
done
