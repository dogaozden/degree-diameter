#!/bin/bash
# usage: screen2.sh START END  (line numbers of shortlist.tsv); appends one line per candidate to screen_out.txt
B=/home/user/degree-diameter/research/squads/raise9/bin
cd /home/user/degree-diameter/research/squads/raise9/r2/f06
sed -n "$1,$2p" shortlist.tsv | while IFS=$'\t' read p k r N mu; do
  out=$(RANDSAMPLE=${SAMPLES:-100} THREADS=1 timeout 60 nice -n 10 $B/haar_gen3s 8 9 0 1 8 /dev/null meta $p $k $r 1 2>&1 | grep RANDSAMPLE | sed 's/.*samples=/samples=/')
  echo "p=$p k=$k r=$r N=$N mu=$mu | ${out:-FAIL}" >> screen_out.txt
done
