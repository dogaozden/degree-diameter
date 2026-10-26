#!/bin/bash
cd /home/user/degree-diameter/research/squads/d3D7-r1/c6
for n in 172 174 176 178 180 182 184 186 188 190 194 196 198 200; do
  sed "s/DumpOrder(170, \"\(.*\)g170.txt\")/DumpOrder($n, \"\1g$n.txt\")/" run.g > run$n.g
  timeout 600 nice -n 10 gap -q -o 1g run$n.g < /dev/null > gap$n.log 2>&1
  timeout 600 nice -n 10 ./cosetdiam g$n.txt /home/user/degree-diameter/research/squads/d3D7-r1/c6/hit >> summary.txt 2>&1
done
echo CHAIN_DONE >> summary.txt
