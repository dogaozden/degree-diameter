#!/bin/bash
# i02 driver 2: scan-based. Fresh scan (random start), then chained scan links (START = previous .best) until cost 0.
# usage: drive2.sh TAG BASE N SEED0 LINKS
H=/home/user/degree-diameter/research/squads/beyond13/r6/i02
cd $H
TAG=$1; BASE=$2; n=$3; S0=$4; LINKS=$5
N=$(( $(head -1 $BASE) * n ))
prev=""
for k in $(seq 0 $LINKS); do
  seed=$((S0+k))
  if [ -n "$prev" ]; then export START=$prev; else unset START; fi
  r=$(timeout 105 nice -n 10 ./scan $BASE $n 14 92 $seed out/${TAG}_k$k 6 2>>out/${TAG}.err | grep RESULT)
  echo "$TAG n=$n N=$N link$k START=${prev:-none} seed=$seed : $r" >> out/${TAG}.log
  prev=$H/out/${TAG}_k$k.best
  case "$r" in *best=0\ *)
     cp $H/out/${TAG}_k$k.edges $H/sol/${TAG}_n${n}_D14_N$N.edges
     timeout 60 nice -n 10 /home/user/degree-diameter/research/frontier/beyond13/bin/apsp $H/sol/${TAG}_n${n}_D14_N$N.edges 3 14 >> out/${TAG}.log 2>&1
     echo "FOUND $TAG n=$n N=$N" >> out/${TAG}.log; break;;
  esac
done
echo DONE >> out/${TAG}.log
