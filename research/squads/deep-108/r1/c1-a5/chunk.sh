#!/bin/bash
# usage: chunk.sh OUT THR START STEP LOG  -- drops a truncated last line of OUT, then runs the card's scanLR command (timeout 100 s)
cd "$(dirname "$0")" || exit 1
. ./env.sh
python3 -c "import sys;f=open(sys.argv[1],'rb+');d=f.read();i=d.rfind(b'\n');f.truncate(i+1 if i>=0 else 0)" "$1" 2>/dev/null
timeout 100 nice -n 10 ../../cq/cq3 59 $A $L $R scanLR "$1" "$2" "$3" "$4" 2> "$5"
echo "exit=$?"
tail -1 "$5"
echo "lines=$(wc -l < "$1")"
