#!/bin/bash
# usage: ladder.sh tag "grp p n" ...   (each group: up to 2 links of 80 s, START-chained)
B=/home/user/degree-diameter/research/frontier/beyond13
C=/home/user/degree-diameter/research/squads/beyond13/r1/c04
tag=$1; shift
cd $C
for spec in "$@"; do
  set -- $spec
  typ=$1; p=$2; n=$3
  out=sols/${typ}_${p}_${n}.sol
  rm -f $out $out.best
  for link in 1 2; do
    if [ $link -eq 1 ]; then st=""; else st="START=$out.best"; fi
    if [ $link -eq 1 ]; then
      ORBIT="3 1 1" THREADS=1 timeout 100 nice -n 10 $B/bin/haar_big0 4 13 80 $((100+link+p)) 8 $out $typ $p $n > runs/${typ}_${p}_${n}_l$link.log 2>&1
    else
      env START=$out.best ORBIT="3 1 1" THREADS=1 timeout 100 nice -n 10 $B/bin/haar_big0 4 13 80 $((200+p)) 8 $out $typ $p $n > runs/${typ}_${p}_${n}_l$link.log 2>&1
    fi
    if grep -q "best=0 " runs/${typ}_${p}_${n}_l$link.log; then break; fi
  done
  echo "$typ $p $n : $(grep RESULT runs/${typ}_${p}_${n}_l*.log | tail -1)" >> runs/ladder_$tag.summary
done
echo DONE >> runs/ladder_$tag.summary
