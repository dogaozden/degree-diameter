#!/bin/bash
# ns_screen.sh LIST SECS SEED OUT.tsv : LIST lines "N m k r s ..." (non-split metacyclic); builds the table, runs haar_tab
T=/home/user/degree-diameter/research/squads/handsoff-49/tools
W=/home/user/degree-diameter/research/squads/handsoff-49/w2
L=$1; S=$2; SEED=$3; OUT=$4
while read N m k r s rest; do
  f=/dev/shm/w2tabs/ns_m${m}_k${k}_r${r}_s${s}.bin
  python3 $W/nonsplit.py --table $m $k $r $s $f
  res=$(timeout 120 nice -n 10 env THREADS=1 $T/haar_tab 4 9 $S $SEED 8 /dev/null tab $f 1 2>&1 | grep -E '^RESULT|error')
  best=$(echo "$res" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
  tm=$(echo "$res" | sed -n 's/.*time=\([0-9.]*\).*/\1/p')
  echo -e "$N\t$m\t$k\t$r\t$s\t${best:-NA}\t${tm:-NA}\t$(echo "$res" | grep -c error)" >> "$OUT"
  rm -f "$f"
done < "$L"
