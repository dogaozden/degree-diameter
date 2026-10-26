#!/bin/bash
# w.sh "p N D secs seed": salift_s over the cyclic group C_N (table cN.txt); appends "best tag n" to res.txt
cd /home/user/degree-diameter/research/squads/own-small/runs/cyc
set -- $1; p=$1; N=$2; D=$3; s=$4; seed=$5; tag=d${D}_p${p}_C${N}_s$seed
D=$D ../../tools/bin/salift_s $p c$N.txt 1 $seed $s 10 0.3 $tag.sol > $tag.log 2>&1
echo "$(grep -o 'best [0-9]*' $tag.log | tail -1 | awk '{print $2}') $tag n=$((2*p*N))" >> res.txt
