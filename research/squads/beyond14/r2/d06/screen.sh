#!/bin/bash
# usage: screen.sh LINEFILE START COUNT SECS SEED
D6=/home/user/degree-diameter/research/squads/beyond14/r2/d06
OC=/home/user/degree-diameter/research/frontier/beyond14/ownsmall
cd $D6
sed -n "$2,$(( $2 + $3 - 1 ))p" $1 | while read N a b s1 s2; do
  tag=$(echo "${s1}_${s2}" | tr ':/' '__')
  T=$D6/tab/$tag.txt; mkdir -p $D6/tab $D6/sols
  if [ ! -s $T ]; then timeout 60 nice -n 10 env THREADS=1 python3 $OC/mktab.py $T "prod:$s1/$s2" >/dev/null 2>&1 || { echo "$N $s1 $s2 TABFAIL"; continue; }; fi
  res=$(timeout 105 nice -n 10 env THREADS=1 D=14 $OC/salift_s 4 $T 1 ${SEED:-1} $4 10 0.3 $D6/sols/$tag.sol 2>&1 | grep -E "^group|end best|FOUND" | tr '\n' ' ')
  echo "$N $s1 $s2 :: $res"
done
