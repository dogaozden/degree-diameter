#!/bin/bash
# screen.sh LISTFILE SECS SEED OUTTSV : run haar_tab 4 9 on each "N m k r ab" line, append "N m k r ab cost time" to OUTTSV
T=/home/user/degree-diameter/research/squads/handsoff-49/tools
L=$1; S=$2; SEED=$3; OUT=$4
mkdir -p /home/user/degree-diameter/research/squads/handsoff-49/w2/sol
while read N m k r ab; do
  f=/home/user/degree-diameter/research/squads/handsoff-49/w2/sol/m${m}_k${k}_r${r}_s${SEED}.sol
  res=$(timeout 120 nice -n 10 env THREADS=1 $T/haar_tab 4 9 $S $SEED 8 $f meta $m $k $r 1 2>&1 | grep '^RESULT' )
  best=$(echo "$res" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
  tm=$(echo "$res" | sed -n 's/.*time=\([0-9.]*\).*/\1/p')
  echo -e "$N\t$m\t$k\t$r\t$ab\t${best:-NA}\t${tm:-NA}" >> "$OUT"
done < "$L"
