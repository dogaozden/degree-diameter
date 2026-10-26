#!/bin/bash
# usage: screen.sh SECONDS SEED BASE PAIRFILE   (PAIRFILE lines: "N I"); appends to screen.txt
S=$1; SEED=$2; BASE=$3; PF=$4
cd /home/user/degree-diameter/research/squads/hunt-d5/r2/b5
while read N I; do
  T=tables/g${N}_${I}.bin
  if [ ! -f $T ]; then
    timeout 300 nice -n 10 python3 ../../tools/gapgroup.py table $N $I $T >/dev/null 2>>gap_err.txt || { echo "TABLEFAIL $N $I" >> screen.txt; continue; }
  fi
  timeout $((S+60)) nice -n 10 ../../tools/flift $BASE $T 7 5 $S $SEED > run_${N}_${I}_s${SEED}.out 2>&1
  R=$(grep RESULT run_${N}_${I}_s${SEED}.out)
  echo "$N $I $(echo "$R" | sed 's/.*best=\([0-9]*\).*/best=\1/') $(echo "$R" | sed 's/.* n=\([0-9]*\).*/n=\1/') seed=$SEED secs=$S" >> screen.txt
done < $PF
