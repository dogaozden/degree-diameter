#!/bin/bash
# usage: screen.sh START END  (1-based line numbers of inv.txt); appends to screen.txt
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
D=/home/user/degree-diameter/research/squads/b48/r3/d04
mkdir -p $D/sol
sed -n "$1,$2p" $D/inv.txt | while read inv N m k r g; do
  out=$D/sol/meta_${m}_${k}_${r}.txt
  res=$(THREADS=1 timeout 20 nice -n 10 $B/haar_fast 4 9 4 1 8 $out meta $m $k $r 1 2>/dev/null | grep '^RESULT')
  echo "inv=$inv N=$N meta $m $k $r g=$g :: $res" >> $D/screen.txt
done
