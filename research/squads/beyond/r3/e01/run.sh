#!/bin/bash
# usage: run.sh "SPEC" ... ; appends one line per group to results.txt
cd /home/user/degree-diameter/research/squads/beyond/r3/e01
for spec in "$@"; do
  name=$(echo "$spec" | tr ' ' '_')
  nice -n 10 python3 mktab.py "$spec" "tabs/$name.bin" > /dev/null || { echo "TABFAIL $spec" >> results.txt; continue; }
  t0=$(date +%s)
  out=$(timeout 900 nice -n 10 ./haar3_exh "tabs/$name.bin" 11 "edges/${name}_n$(python3 -c "import sys;print(2*int(open('tabs/$name.bin','rb').read(4) and __import__('struct').unpack('<i',open('tabs/$name.bin','rb').read(4))[0]))").edges" 2>&1 | tail -2 | tr '\n' ' ')
  t1=$(date +%s)
  echo "$spec | $out | secs=$((t1-t0))" >> results.txt
  rm -f tabs/$name.bin.keep
done
