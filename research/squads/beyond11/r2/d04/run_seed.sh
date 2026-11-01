#!/bin/bash
# usage: run_seed.sh kind p n seed   (kind = sl|psl); writes a random start S (secs=1) and classifies its holes
D4=/home/user/degree-diameter/research/squads/beyond11/r2/d04
B=$D4/haar_hole; export PUSHMAX=${PUSHMAX:-65536}   # smaller push list: same cost, keeps RSS under 0.65 GB
kind=$1; p=$2; n=$3; seed=$4; tag=${kind}${p}_n${n}_s${seed}
if [ ! -s $D4/$tag.sol.start ]; then
  THREADS=1 ORBIT="3 3 2" timeout 105 nice -n 10 $B 11 11 1 $seed 1 $D4/$tag.sol $kind $p $n > $D4/$tag.gen.log 2>&1
fi
THREADS=1 timeout 105 nice -n 10 env CLASS=1 EVAL=$D4/$tag.sol.start $B 11 11 1 $seed 1 $D4/$tag.eval.out $kind $p $n > $D4/$tag.cls.txt 2>$D4/$tag.eval.log
echo "== $tag"; grep -E "^EVAL|^CLASS|^ORDER|^TRACE|^Z |^classify" $D4/$tag.cls.txt
grep -E "^group|start cost" $D4/$tag.gen.log 2>/dev/null
