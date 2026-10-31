#!/bin/bash
# screen.sh TAG SECS TBUDGET TIMEOUT m k r : one metacyclic group through fsd, then APSP check if a SOL appears
cd /home/user/degree-diameter/research/squads/sd5c-r1/c3
TAG=$1; SECS=$2; TB=$3; TO=$4; M=$5; KK=$6; R=$7
FSD=/home/user/degree-diameter/research/selfdual-d5c/src/fsd
timeout $TO nice -n 10 env K=13 TYPES=1,3 SECS=$SECS STOPFIRST=1 MAXSOL=1 TBUDGET=$TB SHUFFLE=1 EDGES=$PWD/edges_$TAG.txt \
  $FSD meta $M $KK $R 1 > out_$TAG.txt 2>&1
echo "exit $?" >> out_$TAG.txt
echo "== $TAG meta $M $KK $R 1 (N=$((M*KK)))"
grep -E "^GROUP|^TABU" out_$TAG.txt | head -30
grep -c "^SOL" out_$TAG.txt | sed 's/^/SOL lines: /'
tail -n 1 out_$TAG.txt
if grep -q "^SOL" out_$TAG.txt && [ -s edges_$TAG.txt ]; then
  echo "APSP:"; timeout 600 nice -n 10 /home/user/degree-diameter/research/selfdual-d5c/src/apsp_mt edges_$TAG.txt 13 5 1 | tail -n 3
fi
