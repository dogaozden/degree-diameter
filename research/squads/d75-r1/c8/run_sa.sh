#!/bin/bash
# run_sa.sh N ID SECS: export SmallGroup(N,ID) (no automorphisms, fast) and run plain annealing haar75 sa.
C=/home/user/degree-diameter/research/squads/d75-r1/c8
T=$C/tmp; mkdir -p $T $C/out
F=$T/g${1}_${2}.ht
TMPDIR=$T timeout 300 nice -n 10 gap -q -o 1g -c "NOAUT:=1;; N:=$1;; ID:=$2;; OUT:=\"$F\";;" /home/user/degree-diameter/research/d75-raise/src/export.g >/dev/null 2>&1
[ -s $F ] || { echo "$1 $2 GAPFAIL"; exit 0; }
SECS=$3 SEED=${4:-1} EDGES=$C/out/sa_$1_$2.edges timeout 900 nice -n 10 /home/user/degree-diameter/research/d75-raise/src/haar75 $F sa > $C/out/sa_$1_$2.log 2>&1
echo "$1 $2 $(grep '^SA best' $C/out/sa_$1_$2.log) $(grep '^SOL' $C/out/sa_$1_$2.log | head -1 | cut -c1-40)"
