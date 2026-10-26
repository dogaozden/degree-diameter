#!/bin/bash
# w4 gated job (one slot, <= 900 s CPU, runs sequentially):
#  1. test: ptlift (parallel tempering) vs plain salift_s2, 5+5 over g81 id 4, D=10, 3 seeds x 25 s each
#  2. screen: ptlift 5+5 over all 15 groups of order 84 (g84.txt), 15 s each
#  3. push: the 2 best order-84 screens continue from their best state (START) for 190 s each, new seed
#  4. every cost-0 state found is turned into edges and checked with score48 EDGES 3 10
W=/home/user/degree-diameter/research/squads/own-small/r2/w4
T=/home/user/degree-diameter/research/squads/own-small/tools
GT=/home/user/degree-diameter/research/squads/own-small/runs/gtxt
cd $W || exit 1
gcc -O2 -o ptlift pt.c -lm || exit 1
export D=10

check() { # check STATE_OR_SOL : edges + score48 (3 10), prints the RESULT line
  local f=$1 N b
  N=$(head -1 "$f" | awk '{print $1}')
  python3 -I $T/best2edges.py $GT/g$N.txt "$f" "$f.edges" > /dev/null || { echo "CHECK $f: best2edges failed"; return; }
  echo "CHECK $f: $($T/bin/score48 "$f.edges" 3 10 | tail -1)"
}

echo "== 1. test 5+5 g81 id4, D=10, 25 s x 3 seeds" > test.log
for s in 1 2 3; do
  $T/bin/salift_s2 5 $GT/g81.txt 4 $s 25 10 0.3 test_plain_$s.sol > test_plain_$s.log 2>&1
  echo "plain salift_s2 seed $s: $(grep 'end best' test_plain_$s.log)" >> test.log
  ./ptlift 5 $GT/g81.txt 4 $s 25 test_pt_$s.sol > test_pt_$s.log 2>&1
  echo "ptlift          seed $s: $(grep 'end best' test_pt_$s.log)" >> test.log
done
# far pairs of the best ptlift state of seed 1 by score48 (cost c should give far = c*N/2 = c*81/2 pairs)
if [ -f test_pt_1.sol.best ]; then
  python3 -I $T/best2edges.py $GT/g81.txt test_pt_1.sol.best test_pt_1.edges > /dev/null
  echo "score48 of test_pt_1.sol.best: $($T/bin/score48 test_pt_1.edges 3 10 | tail -1) (head: $(head -1 test_pt_1.sol.best))" >> test.log
fi
for f in test_*.sol; do [ -f "$f" ] && check "$f" >> test.log; done
cat test.log

echo "== 2. screen p=5 N=84, ptlift 15 s each" > screen.log
: > screen.txt
for id in $(seq 1 15); do
  ./ptlift 5 $GT/g84.txt $id 7 15 scr_$id.sol > scr_$id.log 2>&1
  b=$(grep 'end best' scr_$id.log | awk '{print $3}')
  echo "$id $b" >> screen.txt
  echo "group $id: $(grep 'end best' scr_$id.log)" >> screen.log
  if [ -f scr_$id.sol ]; then check scr_$id.sol >> screen.log; fi
done

echo "== 3. push top 2 of screen" > push.log
top=$(sort -k2,2n -k1,1n screen.txt | head -2 | awk '{print $1}')
for id in $top; do
  START=scr_$id.sol.best ./ptlift 5 $GT/g84.txt $id 99 190 push_$id.sol > push_$id.log 2>&1
  echo "group $id pushed: $(grep 'end best' push_$id.log)" >> push.log
  if [ -f push_$id.sol ]; then check push_$id.sol >> push.log; fi
done
cat screen.log push.log
echo JOB_DONE
