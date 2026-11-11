#!/bin/bash
# evaluates the stored good states (secs=0: no search) with haar_smooth, prints SMSTAT start lines
cd /home/user/degree-diameter/research/squads/handsoff-108/c8c-smooth/gs
i=0
while IFS=$'\t' read -r en S; do
  i=$((i+1))
  printf 'CKPT d=10 evals=0 elapsed=0 best=0\n%s\n' "$S" > st_$i.ckpt
  out=$(ORBIT="3 3 1" ORBW=3 SMSTAT=1 THREADS=1 CKPT=st_$i.ckpt timeout 300 nice -n 10 ../haar_smooth 10 8 0 108961 8 /dev/null psl 23 97 2>&1 | grep "SMSTAT start")
  echo "$i $en $out"
done < list.tsv
