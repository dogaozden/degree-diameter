#!/bin/bash
# usage: scan.sh NAME "GROUPS.PY SPEC"   -> builds NAME.bin, exhaustive class-reduced 2+2 scan at (3,10)
T=/home/user/degree-diameter/research/squads/b48/tools
H=/home/user/degree-diameter/research/squads/b48/r4/h02
cd $H
python3 $T/groups.py "$2" $1.bin > $1.info 2>&1
N=$(head -c 4 $1.bin | od -An -tu4 | tr -d ' ')
echo "$1 spec=[$2] N=$N" 
THREADS=1 nice -n 10 ./gen2 $1.bin 2> $1.gen | THREADS=1 LIMIT=2 ONLYLOW=1 timeout 280 nice -n 10 $T/flift $T/bases/cubic/b22_cubic.txt $1.bin 3 10 eval > $1.out 2> $1.err
echo "$(cat $1.gen) | $(tail -1 $1.err)"
