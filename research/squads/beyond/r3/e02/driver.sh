#!/bin/bash
# e02 driver: one heavy process at a time. Usage: driver.sh SPECFILE  (lines: NAME|SPEC)
G=/home/user/degree-diameter/research/squads/b48/tools/groups.py
R=/home/user/degree-diameter/research/squads/beyond/r1/c12/tables
HERE=/home/user/degree-diameter/research/squads/beyond/r3/e02
cd $HERE
while IFS='|' read -r name spec; do
  [ -z "$name" ] && continue
  bin=$HERE/tab_$name.bin
  if [ -f $R/$name.bin ]; then bin=$R/$name.bin; else
    timeout 900 nice -n 10 python3 $G "$spec" $bin > gen_$name.log 2>&1 || { echo "$name GEN_FAIL" >> run_all.txt; continue; }
  fi
  timeout 900 nice -n 10 ./exh3 $bin 12 $HERE/found_$name > out_$name.txt 2>&1 || echo "$name EXH_TIMEOUT_OR_FAIL" >> run_all.txt
  grep -h "GROUP\|RESULT\|WROTE" out_$name.txt >> run_all.txt
  case $bin in $HERE/*) rm -f $bin;; esac
done < "$1"
echo DRIVER_DONE >> run_all.txt
