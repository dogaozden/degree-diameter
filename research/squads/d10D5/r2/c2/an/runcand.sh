#!/bin/bash
# usage: runcand.sh P:L ... ; runs dmhub coverage-only annealing on base8 for each candidate, prints final cover cost
cd /home/user/degree-diameter/research/squads/d10D5/r2/c2
F0="266 41 225 65 263 283 398 253"
for c in "$@"; do
  p=${c%%:*}
  tag=c_${p}_$(echo $c | tr ':' '_')
  s=$(date +%s)
  FORCE="$c" FREE="$F0 $p" COVIT=2000000 CT0=0.25 ITERS=0 NOHUBG=1 SEED=1 timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin base8.lift2.sol $tag > log_$tag.txt 2>&1
  e=$(date +%s)
  echo "$c final: $(grep 'cover cost final' log_$tag.txt) wall $((e-s))s"
done
