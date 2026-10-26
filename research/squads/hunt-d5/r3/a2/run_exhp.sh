#!/bin/bash
# run_exhp.sh OUTLOG "N i" ... : exhaustive Delta=5 Haar search (haar5 exhp) for each SmallGroup(N,i), single-threaded
T=../../tools
LOG=$1; shift
while [ $# -ge 2 ]; do
  n=$1; i=$2; shift 2
  f=g${n}_${i}.bin
  [ -f $f ] || timeout 300 nice -n 10 python3 $T/gapgroup.py table $n $i $f || { echo "$n $i :: TABLE FAILED" >> $LOG; continue; }
  r=$(OMP_NUM_THREADS=1 THREADS=1 timeout 600 nice -n 10 $T/haar5 exhp $f 5 0 | tail -1)
  echo "$n $i :: $r" >> $LOG
  rm -f $f
done
echo CHUNK_DONE >> $LOG
