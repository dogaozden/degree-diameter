#!/bin/bash
# usage: batch.sh SECS "n:lam:seed[:startfile]" ...   runs two at a time, appends RESULT lines to log
F=/home/user/degree-diameter/research/frontier
E=/home/user/degree-diameter/research/squads/beyond15/r2/e02
SECS=$1; shift
run1() {
  IFS=: read n lam seed st <<< "$1"
  pre=$E/runs/f18_n${n}_l${lam}_s${seed}
  if [ -n "$st" ] && [ "$st" != "-" ]; then
    out=$(env THREADS=1 T0=2 T1=0.05 L=1200 START=$st nice -n 10 $F/bin/liftsym $F/beyond15/lsym/foster18.txt $F/beyond15/lsym/foster18.perm $n $lam 16 $SECS $seed $pre 2>/dev/null)
  else
    out=$(env THREADS=1 T0=2 T1=0.05 L=1200 nice -n 10 $F/bin/liftsym $F/beyond15/lsym/foster18.txt $F/beyond15/lsym/foster18.perm $n $lam 16 $SECS $seed $pre 2>/dev/null)
  fi
  echo "$out" | tee -a $E/runs/log.txt
}
while [ $# -gt 0 ]; do
  run1 "$1" & shift
  if [ $# -gt 0 ]; then run1 "$1" & shift; fi
  wait
done
