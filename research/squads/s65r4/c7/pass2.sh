#!/bin/bash
DIR=/home/user/degree-diameter/research/squads/s65r4/c7
T=/home/user/degree-diameter/research/s65/tools
cd $DIR
until grep -q PASS1_DONE summary.txt; do sleep 5; done
# top 3 pass-1 pairs by best cost
awk '/RESULT best/{print $4, $1}' summary.txt | sort -n -k1,1 | head -3 > top3.txt
echo "TOP3:" >> pass2.log; cat top3.txt >> pass2.log
while read COST TAG; do
  G=$(echo $TAG | sed -E 's/^g([0-9]+_[0-9]+)_b([0-9])_.*/\1/')
  B=$(echo $TAG | sed -E 's/^g([0-9]+_[0-9]+)_b([0-9])_.*/\2/')
  ./run1.sh $G $B 240 2
done < top3.txt
echo PASS2_DONE >> summary.txt
# exact 2-opt on finals with cost <= 6 (pass 1 and pass 2)
for SOL in g*_s*.sol; do
  TAG=${SOL%.sol}
  BEST=$(awk -v t="$TAG" '$1==t && /RESULT best/{print $4}' summary.txt)
  [ -z "$BEST" ] && BEST=$(grep -o 'RESULT best [0-9]*' $TAG.out | awk '{print $3}')
  if [ -n "$BEST" ] && [ "$BEST" -le 6 ] && [ "$BEST" -gt 0 ]; then
    G=$(echo $TAG | sed -E 's/^g([0-9]+_[0-9]+)_b.*/\1/')
    timeout 120 nice -n 10 $T/kopt $DIR/$SOL $T/../groups/sg/sg_$G.txt 2 5 > $TAG.k2 2> $TAG.k2.err
    echo "KOPT $TAG cost=$BEST blocks=$(grep -c '^SOL' $TAG.k2)" >> pass2.log
  fi
done
echo KOPT_DONE >> pass2.log
echo ALL_DONE >> summary.txt
