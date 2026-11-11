#!/bin/bash
# usage: screen.sh START END  (line numbers of cands.tsv); prints RANDSAMPLE line per candidate
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r2/f06
sed -n "$1,$2p" cands.tsv | while IFS=$'\t' read p k r N mu; do
  out=$(RANDSAMPLE=${SAMPLES:-200} THREADS=1 timeout 60 nice -n 10 $B/haar_gen3s 8 9 0 1 8 /dev/null meta $p $k $r 1 2>&1 | grep RANDSAMPLE)
  echo "$p $k $r $N $mu | $out"
done >> screen_out.txt
