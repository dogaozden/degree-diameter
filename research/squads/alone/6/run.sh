#!/bin/bash
# run.sh k m n r iters seed T0 T1 tag : one annealing job; appends one scoreboard line; verifies valid finds with apsp.
cd "$(dirname "$0")"
k=$1; m=$2; n=$3; r=$4; it=$5; seed=$6; T0=$7; T1=$8; tag=$9
out=out/${tag}.txt
line=$(./out/vlift $k $m $n $r $it $seed $T0 $T1 $out 2>/dev/null | head -1)
cost=$(echo "$line" | sed -n 's/.*cost=\([0-9]*\).*/\1/p')
N=$((2*k*m*n))
cmd="./out/vlift $k $m $n $r $it $seed $T0 $T1 $out"
if [ "$cost" = "0" ]; then
  res=$(./out/apsp $out 16 5 | tail -1)
  case "$res" in *VALID*) valid=true;; *) valid=false;; esac
  echo "{\"idea\": \"voltage lift, circulant base k=$k (2k=$((2*k)) vertices), G=Z_$m x|_$r Z_$n\", \"command\": \"$cmd\", \"score\": $N, \"valid\": $valid}" >> scoreboard.jsonl
  echo "$tag: N=$N cost=0 apsp=$res" 
else
  echo "{\"idea\": \"voltage lift, circulant base k=$k (2k=$((2*k)) vertices), G=Z_$m x|_$r Z_$n\", \"command\": \"$cmd\", \"score\": ${cost:-null}, \"valid\": false}" >> scoreboard.jsonl
  echo "$tag: N=$N cost=$cost"
fi
