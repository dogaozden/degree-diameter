#!/bin/bash
# screen.sh N:I ...  -> builds table of SmallGroup(N,I), runs haar_tab d=7 D=5, seeds 1 and 2, 6 s each; appends to screen.tsv
cd "$(dirname "$0")"
for pair in "$@"; do
  N=${pair%%:*}; I=${pair##*:}
  T=tabs/g${N}_${I}.bin
  [ -f $T ] || timeout 200 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T || { echo -e "$N\t$I\tTABLEFAIL" >> screen.tsv; continue; }
  for seed in 1 2; do
    r=$(THREADS=1 OMP_NUM_THREADS=1 COOL=10 REHEAT=40 timeout 40 nice -n 10 ../../tools/haar_tab 7 5 6 $seed 16 tabs/s${N}_${I}_${seed}.sol tab $T 1 2>&1 | grep RESULT)
    b=$(echo "$r" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
    echo -e "$N\t$I\tseed$seed\tbest=${b:-NA}" >> screen.tsv
  done
done
echo CHUNKDONE "$@" >> screen.tsv
