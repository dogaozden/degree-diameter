#!/bin/bash
# sweep.sh N : exhaustive pair scan (S={0,x,y}) over all metacyclic groups of order N; prints successful groups
N=$1
python3 groups_list.py $N | awk '$1>1 && $2>=1 {print $1, $2, $3}' | while read m k r; do
  out=$(timeout 900 nice -n 10 ./haar_meta $m $k $r 11 scan 0)
  case "$out" in *"good=0 "*) ;; *) echo "$out";; esac
done
