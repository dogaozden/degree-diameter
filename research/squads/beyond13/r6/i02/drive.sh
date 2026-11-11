#!/bin/bash
# i02 driver: one stream per argument list. Fresh lift anneal (95 s), then up to 2 scan chain links while cost > 0.
# usage: drive.sh TAG BASE_FILE "n1 n2 ..." 
H=/home/user/degree-diameter/research/squads/beyond13/r6/i02; B=/home/user/degree-diameter/research/frontier/beyond13
cd $H
TAG=$1; BASE=$2; NS=$3
for n in $NS; do
  N=$(( $(head -1 $BASE) * n ))
  fresh=$(timeout 105 nice -n 10 $B/bin/lift $BASE $n 14 92 7$n $H/out/${TAG}_n$n 8 1 400 2>>$H/out/${TAG}.err | grep RESULT)
  echo "$TAG n=$n N=$N fresh: $fresh" >> $H/out/${TAG}.log
  cost=$(echo "$fresh" | sed -n 's/.*best=\([0-9]*\).*/\1/p')
  prev=$H/out/${TAG}_n$n.best
  if [ "$cost" = "0" ]; then
     cp $H/out/${TAG}_n$n.edges $H/sol/${TAG}_n${n}_D14_N$N.edges; echo "FOUND $TAG n=$n" >> $H/out/${TAG}.log; continue
  fi
  for k in 1 2; do
    r=$(START=$prev timeout 105 nice -n 10 ./scan $BASE $n 14 92 $((n*10+k)) $H/out/${TAG}_n${n}c$k 6 2>>$H/out/${TAG}.err | grep RESULT)
    echo "$TAG n=$n chain$k: $r" >> $H/out/${TAG}.log
    prev=$H/out/${TAG}_n${n}c$k.best
    case "$r" in *best=0\ *) cp $H/out/${TAG}_n${n}c$k.edges $H/sol/${TAG}_n${n}_D14_N$N.edges; echo "FOUND $TAG n=$n chain$k" >> $H/out/${TAG}.log; break;; esac
  done
done
echo DONE >> $H/out/${TAG}.log
