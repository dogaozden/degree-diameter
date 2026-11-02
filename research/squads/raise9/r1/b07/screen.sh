#!/bin/bash
# usage: screen.sh d D ORBITSPEC candfile samples
B=/home/user/degree-diameter/research/squads/raise9/bin
d=$1; D=$2; OR=$3; F=$4; M=${5:-20}
while read fam rest; do
  case "$fam" in
    sl|psl) ;;
    *) continue;;
  esac
  q=$(echo "$rest" | awk '{print $1}')
  n=$(echo "$rest" | sed -n 's/.*n=\([0-9]*\).*/\1/p')
  N=$(echo "$rest" | sed -n 's/.*N=\([0-9]*\).*/\1/p')
  pe=$(echo "$rest" | grep -c 'p^')
  if [ "$pe" = "1" ]; then
    # prime power: haar_sym
    tag="${fam}_${q}_pp_n${n}"
    out=/home/user/degree-diameter/research/squads/raise9/r1/b07/s_${tag}.txt
    res=$(THREADS=1 ORBIT="$OR" RANDORB=$M timeout 60 nice -n 10 $B/haar_sym $d $D 5 1 4 $out $fam $q $n 2>&1 | grep 'RANDORB d=' )
  else
    tag="${fam}_${q}_n${n}"
    out=/home/user/degree-diameter/research/squads/raise9/r1/b07/s_${tag}.txt
    res=$(THREADS=1 ORBIT="$OR" RANDORB=$M timeout 60 nice -n 10 $B/haar_big0 $d $D 5 1 4 $out $fam $q $n 2>&1 | grep 'RANDORB d=' )
  fi
  echo "$fam q=$q n=$n N=$N :: $res" | sed 's/RANDORB d=[^ ]* D=[^ ]* //'
done < "$F"
