#!/bin/bash
# sweep: k=73, n=9491 (prime, 9491 = 1 mod 73), lambda exact order 73, EXH over gauge classes
cd /home/user/degree-diameter/research/squads/beyond15/r4/w04
F=/home/user/degree-diameter/research/frontier
n=9491; k=73
lam=$(python3 lam.py $n $k)
i=0
while read S; do
  i=$((i+1))
  tag=k73_n${n}_p$i
  python3 mkbase.py $k "$S" out/$tag.base out/$tag.perm
  start=$(date +%s)
  THREADS=1 EXH=1 timeout 1500 $F/bin/liftsym out/$tag.base out/$tag.perm $n $lam 15 1000 1 out/$tag > out/$tag.log 2>&1
  echo "pattern $S lam $lam elapsed $(( $(date +%s) - start ))s : $(grep EXHRESULT out/$tag.log)" >> out/sweep73.summary
done < pats73.txt
echo DONE >> out/sweep73.summary
