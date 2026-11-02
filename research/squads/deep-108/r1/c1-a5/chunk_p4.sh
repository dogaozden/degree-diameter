#!/bin/bash
# usage: chunk_p4.sh START STEP LOG  -- P4 family (L = <(r,r2),(t,t)>, R = <(r,r2),(I,s)>), out p4.tsv, THR 300, timeout 100 s
cd "$(dirname "$0")" || exit 1
. ./env.sh
LG="2 $r $r2 $t $t"; RG="2 $r $r2 $I $s"
python3 -c "import sys;f=open('p4.tsv','rb+');d=f.read();i=d.rfind(b'\n');f.truncate(i+1 if i>=0 else 0)" 2>/dev/null
timeout 100 nice -n 10 ../../cq/cq3 59 $A $LG $RG scanLR p4.tsv 300 "$1" "$2" 2> "$3"
echo "exit=$?"
tail -1 "$3"
echo "lines=$(wc -l < p4.tsv)"
