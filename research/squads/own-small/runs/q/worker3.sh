#!/bin/bash
# worker3.sh "p N id D secs seed GROUPSFILE": one cubic salift_s run; logs and states in runs/q/c3/
cd /home/user/degree-diameter/research/squads/own-small/runs/q; mkdir -p c3
set -- $1; p=$1; N=$2; id=$3; D=$4; s=$5; seed=$6; gf=$7; tag=c3/d${D}_p${p}_N${N}_g${id}_s$seed
D=$D ../../tools/bin/salift_s $p $gf $id $seed $s 10 0.3 $tag.sol > $tag.log 2>&1
echo "$(grep -o 'best [0-9]*' $tag.log | tail -1) $tag" >> results3.txt
