#!/bin/bash
# fresh.sh N I SEED0 NSEEDS: fresh haar_tab d=7 D=5 seeds, 6 s each, appends to fresh.tsv; cost 0 writes tabs/f<N>_<I>_<seed>.sol
cd "$(dirname "$0")"
N=$1; I=$2; s0=$3; ns=$4; T=tabs/g${N}_${I}.bin
for ((s=s0; s<s0+ns; s++)); do
  r=$(THREADS=1 OMP_NUM_THREADS=1 COOL=10 REHEAT=40 timeout 40 nice -n 10 ../../tools/haar_tab 7 5 6 $s 16 tabs/f${N}_${I}_${s}.sol tab $T 1 2>&1 | grep RESULT)
  b=$(echo "$r" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  echo -e "$N\t$I\tseed$s\tbest=${b:-NA}" >> fresh.tsv
done
echo FRESHDONE $N $I >> fresh.tsv
