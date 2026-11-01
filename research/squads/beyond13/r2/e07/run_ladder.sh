#!/bin/bash
# e07 (5,14): haar_gen3 random S, 88 s per candidate, sizes just above the record N = 5,848,428 (2N = 11,696,856).
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r2/e07
for spec in "sl 29 241" "psl 53 79" "psl 25 757" "psl 27 601" "psl 31 397" "psl 29 487" "psl 43 151" "psl 229 1" "sl 181 1" "psl 73 31"; do
  set -- $spec
  fam=$1; q=$2; n=$3; tag=${fam}_${q}_${n}
  timeout 100 nice -n 10 env THREADS=1 $B/bin/haar_gen3 5 14 88 11 8 ./sol_${tag}.txt $fam $q $n > ./log_${tag}.log 2>&1
  r=$(grep RESULT ./log_${tag}.log | tail -1)
  if grep -q 'best=0 ' ./log_${tag}.log; then
    timeout 300 nice -n 10 $B/bin/haarcheck_gen ./sol_${tag}.txt > ./sol_${tag}.gen.txt 2>&1
    echo "$tag SOLVED $(tail -1 ./sol_${tag}.gen.txt) :: $r" >> ./summary.txt
  else
    echo "$tag $r" >> ./summary.txt
  fi
done
echo DONE >> ./summary.txt
