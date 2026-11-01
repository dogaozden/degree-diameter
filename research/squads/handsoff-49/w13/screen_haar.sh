#!/bin/bash
# screen_haar.sh LISTFILE SECS SEED OUTTSV : haar_tab 4 9 on each "N m k r" line (copy of w2's screen, own output)
T=/home/user/degree-diameter/research/squads/handsoff-49/tools
L=$1; S=$2; SEED=$3; OUT=$4
while read N m k r; do
  f=/home/user/degree-diameter/research/squads/handsoff-49/w13/sol/m${m}_k${k}_r${r}_s${SEED}.sol
  res=$(timeout 120 nice -n 10 env THREADS=1 $T/haar_tab 4 9 $S $SEED 8 $f meta $m $k $r 1 2>&1 | grep '^RESULT')
  best=$(echo "$res" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
  printf "%s\t%s\t%s\t%s\t%s\n" "$N" "$m" "$k" "$r" "${best:-NA}" >> "$OUT"
done < "$L"
