#!/bin/bash
# usage: run_screen.sh SPECFILE SECONDS SEED OUTLOG   (specfile lines: p k r n ; one per line)
SPECS=$1; SECS=$2; SEED=$3; LOG=$4
cd /home/user/degree-diameter/research/squads/hunt-d5/r3/c4 || exit 1
mkdir -p out
while read p k r n; do
  [ -z "$p" ] && continue
  tag="p${p}_k${k}_r${r}_n${n}_s${SEED}"
  res=$(THREADS=1 COOL=${COOL:-3} timeout $((SECS*3+60)) nice -n 10 ../../tools/haar_fast 9 5 $SECS $SEED 16 out/$tag.bin meta $p $k $r $n 2>&1 | grep RESULT)
  echo "$p $k $r $n seed=$SEED :: $res" >> "$LOG"
done < "$SPECS"
