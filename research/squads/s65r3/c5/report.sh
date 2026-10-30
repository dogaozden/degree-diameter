#!/bin/bash
# cost distribution per order and best candidate, from summary.txt
C=/home/user/degree-diameter/research/squads/s65r3/c5
cd $C
echo "runs: $(wc -l < summary.txt)"
for ord in 176 180; do
  echo "order $ord costs: $(awk -v o=$ord '$1 ~ "^sg_"o"_" && $4!="NA" {print $4}' summary.txt | sort -n | uniq -c | awk '{printf "%s x%s; ", $2, $1}')"
done
echo "best per pair (cost k2found):"
awk '$4!="NA"{k=$1" "$2; if(!(k in b)||$4<b[k]){b[k]=$4; s[k]=$3; f[k]=$5}} END{for(k in b) print b[k], k, "seed", s[k], "k2", f[k]}' summary.txt | sort -n | head -6
echo "k2 found in any run: $(awk '$5>0' summary.txt | wc -l)"
echo "candidates:"; cat candidates.txt 2>/dev/null | tail -20
