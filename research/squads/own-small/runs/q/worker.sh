#!/bin/bash
# worker.sh "p N id D secs": one salift4 run; logs and states in runs/q/
cd /home/user/degree-diameter/research/squads/own-small/runs/q
set -- $1; p=$1; N=$2; id=$3; D=$4; s=$5; tag=d${D}_p${p}_N${N}_g${id}
D=$D ../../tools/bin/salift4 $p g$N.txt $id 1 $s 10 0.3 $tag.sol > $tag.log 2>&1
echo "$(grep -o 'best [0-9]*' $tag.log | tail -1) $tag" >> results.txt
