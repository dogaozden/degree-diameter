#!/bin/bash
# runs SKIPPATCH coverage anneal for each "P:L:SEED:CT0" spec, then relaxed check; prints one line per run
cd /home/user/degree-diameter/research/squads/d10D5/r2/c2
F0="266 41 225 65 263 283 398 253"
for spec in "$@"; do
  IFS=: read p l seed ct0 <<< "$spec"
  tag=s${p}_${seed}
  s=$(date +%s)
  FORCE="$p:$l" FREE="$F0 $p" SKIPPATCH=1 COVIT=3000000 CT0=$ct0 ITERS=0 NOHUBG=1 SEED=$seed timeout 400 nice -n 10 ./dmhub gq/gq_q7.bin base8.lift2.sol $tag > log_$tag.txt 2>&1
  python3 sol2lift2.py $tag.sol ${tag}_l2.sol > /dev/null
  rel=$(FREE="$F0 $p" RELAX=1 PATCH=1 IN=${tag}_l2.sol BASE=gq/gq_q7.bin NPOLY=4 ITERS=0 timeout 300 nice -n 10 ./dmfast_hub 7 2>&1 | grep -E 'relaxed' )
  e=$(date +%s)
  echo "$spec: $(grep 'cover cost final' log_$tag.txt) | $rel | wall $((e-s))s"
done
echo DONE
