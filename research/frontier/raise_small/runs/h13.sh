#!/bin/bash
# exhaustive cubic Haar graphs H(G,{e,x,y}) at D=13 over odd-order metacyclic groups (exh3, beyond-etos3t)
cd /home/user/degree-diameter/research/frontier/raise_small; mkdir -p runs/H13
while read N m k r d f; do
  python3 tools/mkbin.py $m $k $r runs/H13/t.bin
  echo "meta $m $k $r d=$d | $(timeout 600 bin/exh3 runs/H13/t.bin 13 runs/H13/hit_${m}_${k}_${r} | grep GROUP)" >> runs/H13/sweep.txt
done < runs/h13_odd.txt
rm -f runs/H13/t.bin
