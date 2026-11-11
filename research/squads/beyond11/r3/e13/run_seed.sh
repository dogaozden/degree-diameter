#!/bin/bash
# usage: run_seed.sh kind p n seed   (kind = sl|psl). Even-D (d,D) = (8,12), ORBIT "3 2 2" (f=2, m=2, |S|=8).
# Writes a random start S (secs=1, <out>.sol.start) and classifies its holes with CLASS=1.
E13=/home/user/degree-diameter/research/squads/beyond11/r3/e13
B=/home/user/degree-diameter/research/squads/beyond11/r2/d04/haar_hole
export PUSHMAX=65536
kind=$1; p=$2; n=$3; seed=$4; tag=${kind}${p}_n${n}_s${seed}
if [ ! -s $E13/$tag.sol.start ]; then
  THREADS=1 ORBIT="3 2 2" timeout 105 nice -n 10 $B 8 12 1 $seed 1 $E13/$tag.sol $kind $p $n > $E13/$tag.gen.log 2>&1
fi
THREADS=1 timeout 105 nice -n 10 env CLASS=1 EVAL=$E13/$tag.sol.start $B 8 12 1 $seed 1 $E13/$tag.eval.out $kind $p $n > $E13/$tag.cls.txt 2> $E13/$tag.eval.log
echo "== $tag"; grep -E "^EVAL|^CLASS|^ORDER|^Z " $E13/$tag.cls.txt
grep -E "^group|alpha:|start cost|classify" $E13/$tag.gen.log $E13/$tag.eval.log 2>/dev/null
