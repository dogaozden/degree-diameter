#!/bin/bash
# card c2 step 3: exact-cost hub build + BFS annealing (dmhub) on the relaxed k=6 solution, then scorer if cost 0.
cd /home/user/degree-diameter/research/squads/d10D5/r1/c2
while kill -0 4278 2>/dev/null; do sleep 2; done          # wait for step 2 (dmfast_hub) to finish
FREE="$(cat def2_s1.sol.free)" COVIT=200000 CT0=0.3 ITERS=300000 PNU=0.5 PTARG=0.9 FOCUS=0.8 T0=0.5 T1=0.03 \
    SECS=330 SEED=1 THREADS=1 timeout 480 nice -n 10 ./dmhub gq/gq_q7.bin def2_s1_k2.sol d6a > d6a.log 2>&1
grep -E "matching|hub graph|initial cost|cover cost|final cost" d6a.log | tail -8
if grep -q "final cost 0 " d6a.log; then
    timeout 300 nice -n 10 ./apsp d6a.edges 10 5
else
    echo "NOT COST 0 (see d6a.log)"
fi
echo STEP3_DONE
