#!/bin/bash
# c08 ladder: haar_gen3 random-S search for (5,14), 90 s per candidate, one thread, then independent check of any cost-0 file
B=/home/user/degree-diameter/research/frontier/beyond13
cd /home/user/degree-diameter/research/squads/beyond13/r1/c08
for spec in "psl 31 433" "sl 37 127" "psl 17 2659" "psl 17 2719" "psl 19 1951" "sl 29 277"; do
  set -- $spec
  fam=$1; p=$2; n=$3; tag=${fam}_${p}_${n}
  timeout 100 nice -n 10 env THREADS=1 $B/bin/haar_gen3 5 14 90 7 8 ./lad_${tag}.txt $fam $p $n > ./lad_${tag}.log 2>&1
  if grep -q 'best=0 ' ./lad_${tag}.log; then
    timeout 900 nice -n 10 $B/bin/haarcheck_gen ./lad_${tag}.txt > ./lad_${tag}.gen.txt 2>&1
    echo "$tag SOLVED $(tail -1 ./lad_${tag}.gen.txt)" >> ./ladder_summary.txt
  else
    echo "$tag $(grep RESULT ./lad_${tag}.log | tail -1)" >> ./ladder_summary.txt
  fi
done
echo DONE >> ./ladder_summary.txt
