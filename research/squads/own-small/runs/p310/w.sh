#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/runs/p310
set -- $1; p=$1; N=$2; id=$3; seed=$4; gf=$5; tag=p${p}_N${N}_g${id}_s$seed
D=10 ../../tools/bin/salift_s $p $gf $id $seed 60 10 0.3 $tag.sol > $tag.log 2>&1
echo "$(grep -o 'best [0-9]*' $tag.log | tail -1 | awk '{print $2}') $tag" >> res.txt
