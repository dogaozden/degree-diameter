#!/bin/bash
# usage: screen.sh LIST SEED SECONDS ; LIST lines: "idx"
cd /home/user/degree-diameter/research/squads/hunt-d5/r6/b2
TOOL=../../tools
while read I; do
  [ -f g608_$I.bin ] || timeout 300 nice -n 10 python3 $TOOL/gapgroup.py table 608 $I g608_$I.bin >/dev/null 2>&1
  OUT=s$2_g$I.sol
  line=$(SAVEBEST=1 COOL=10 REHEAT=40 THREADS=1 timeout $(( ${3%.*} + 40 )) nice -n 10 $TOOL/haar_tab 7 5 $3 $2 16 $OUT tab g608_$I.bin 1 2>&1 | grep RESULT | tail -1)
  echo "idx=$I seed=$2 $line"
done < $1
