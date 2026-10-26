#!/bin/bash
# non-cyclic groups of orders 65..75, largest order first; top-4 bases from the cyclic screen; 1 s per run
export OMP_NUM_THREADS=1 THREADS=1
cd /home/user/degree-diameter/research/squads/hunt-d5/r1/a3
mkdir -p tables runs
TOOLS=../../tools
for N in 75 74 73 72 71 70 69 68 67 66 65; do
  grep -E "^$N " groups_all.txt | while read n i ab rest; do
    sname=$(echo "$rest" | sed -E 's/.*"(.*)".*/\1/')
    if [ "$sname" = "C$N" ]; then continue; fi
    tb=tables/g${N}_${i}.bin
    [ -f "$tb" ] || timeout 120 nice -n 10 python3 $TOOLS/gapgroup.py table $N $i $tb </dev/null || { echo "TABLEFAIL $N $i"; continue; }
    for b in b11 b10 b12 b08; do
      timeout 20 nice -n 10 $TOOLS/flift bases/$b.txt $tb 5 5 1 $((N*1000+i*10+1)) 8 runs/nc_${N}_${i}_$b.out </dev/null 2>&1 | grep RESULT | sed "s/^/$b N=$N i=$i [$sname] /"
    done
  done
done
echo DONE
