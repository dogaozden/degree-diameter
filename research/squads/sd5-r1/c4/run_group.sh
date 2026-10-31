#!/bin/bash
# usage: run_group.sh N ID TIMEOUT_SECS ; exports bi-coset data, runs bic75 (DELTA=6), verifies any solution with apsp
C=/home/user/degree-diameter/research/squads/sd5-r1/c4
N=$1; ID=$2; TO=${3:-240}
export TMPDIR=$C/tmp
G=$C/bic/g${N}_${ID}.ht
timeout 300 nice -n 15 gap -q -c "N:=$N;; ID:=$ID;; OUT:=\"$G\";; INVS:=1;; NOAUT:=1;;" /home/user/degree-diameter/research/d75-raise/src/export.g </dev/null >/dev/null 2>&1
S=$(date +%s)
DELTA=6 EDGES=$C/bic/g${N}_${ID}.edges MAXEV=20000000 timeout $TO nice -n 15 $C/bic/bic75 $G > $C/logs/g${N}_${ID}.out 2>&1
RC=$?
echo "secs $(( $(date +%s) - S )) rc $RC" >> $C/logs/g${N}_${ID}.out
if [ -f $C/bic/g${N}_${ID}.edges ]; then
  /home/user/degree-diameter/research/selfdual-d5/src/apsp $C/bic/g${N}_${ID}.edges 6 5 | tail -2 >> $C/logs/g${N}_${ID}.out
fi
rm -f $G
