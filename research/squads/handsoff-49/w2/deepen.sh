#!/bin/bash
# deepen.sh LISTFILE SECS SEEDS... : LISTFILE lines "N m k r ab"; runs haar_tab for each seed, appends "N m k r seed best time" to deep.tsv
T=/home/user/degree-diameter/research/squads/handsoff-49/tools
W=/home/user/degree-diameter/research/squads/handsoff-49/w2
L=$1; S=$2; shift 2
mkdir -p $W/sol
while read N m k r ab; do
  for SEED in "$@"; do
    f=$W/sol/deep_m${m}_k${k}_r${r}_s${SEED}_t${S}.sol
    res=$(timeout 200 nice -n 10 env THREADS=1 $T/haar_tab 4 9 $S $SEED 8 $f meta $m $k $r 1 2>&1 | grep '^RESULT')
    best=$(echo "$res" | sed -n 's/.*best=\([0-9-]*\).*/\1/p')
    tm=$(echo "$res" | sed -n 's/.*time=\([0-9.]*\).*/\1/p')
    echo -e "$N\t$m\t$k\t$r\t$ab\t$SEED\t${best:-NA}\t${tm:-NA}\t$S" >> $W/deep.tsv
    if [ "$best" = "0" ]; then echo "COST0 $N $m $k $r seed $SEED" >> $W/cost0.txt; fi
  done
done < "$L"
