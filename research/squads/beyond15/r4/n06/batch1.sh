#!/bin/bash
# anneal batch: D=15 k=5 patterns x admissible n (secs each)
LS=/home/user/degree-diameter/research/frontier/beyond15/lsym/qg
L=/home/user/degree-diameter/research/frontier/bin/liftsym
O=/home/user/degree-diameter/research/squads/beyond15/r4/n06/out
D=$1; SECS=$2; shift 2
for pat in "$@"; do
  B=$(ls $LS | grep -E "_k5_${pat}\.txt" | sed 's/\.txt//')
  for nl in "401 39" "421 252" "410 51" "400 81"; do
    set -- $nl
    THREADS=1 nice -n 10 $L $LS/$B.txt $LS/$B.perm $1 $2 $D $SECS 7 $O/k5_${pat}_n$1 2>&1 | grep -E "RESULT|EXHRESULT" | sed "s/^/pat $pat n $1 l $2 /" >> $O/../log_batch1.txt
  done
done
echo batchdone >> $O/../log_batch1.txt
