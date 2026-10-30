#!/bin/bash
# usage: screen.sh LOG  (reads lines "BASE GROUP TAG" from stdin, runs vl with SECS=20)
LOG=$1
while read -r base grp tag; do
  out=sols/${tag}.txt
  res=$(D=5 SECS=${SECS:-20} SEED=${SEED:-1} OUT=$out timeout 900 nice -n 10 ./vl bases/$base.txt grp/$grp.txt 2>/dev/null | grep RESULT)
  echo "$tag $base $grp :: $res" | tee -a $LOG
done
