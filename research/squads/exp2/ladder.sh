#!/bin/bash
# usage: ladder.sh D d "ORBIT spec" SECS tag  "grp args ... n" ...   (candidates in increasing order; stops at first failure)
# each candidate: run haar_sym; on RESULT best=0 write solution and continue; else stop.
here=$(cd "$(dirname "$0")" && pwd); S=$here/src/haar_sym
D=$1; d=$2; ORB=$3; SECS=$4; TAG=$5; shift 5
for cand in "$@"; do
  set -- $cand; n=${@: -1}; grp=("${@:1:$#-1}")
  name="d${d}D${D}_${TAG}_$(echo ${grp[*]} | tr ' ' '_')x${n}"
  log=$here/runs/$name.log; out=$here/sols/$name.txt
  ORBIT="$ORB" THREADS=1 timeout $((SECS+120)) $S $d $D $SECS 1 8 "$out" "${grp[@]}" "$n" > "$log" 2>&1
  if grep -q "best=0 " "$log"; then echo "OK $name $(grep RESULT "$log" | tail -1)"; else echo "FAIL $name $(grep -o 'best=[0-9]*' "$log" | tail -1)"; break; fi
done
