#!/bin/bash
# card c2 (squad d16D10-r2): SL(2,61) x Z10141, ORBIT="5 3 1", K 4, 600 s runs.
# Run 1 (seed 1, default schedule, fresh start) ended at cost 12 and was still descending at the end (the greedy regime
# T = 0.15 from step ~13 on; best 21 -> 12 between steps 23 and 44). Run 2 is a continuation of run 1: START from run 1's
# best S with a new seed (2), and TMAX = TMIN = 0.15 so the temperature stays at the greedy floor from the first step
# (with the default TMAX 1.5 the restart would first wander away from the start S).
# EVAL of run 1's best, run 2 and EVAL of run 2's best all run inside ONE slot.sh hold (one slot wait, one heavy job at a time).
HB=/tmp/claude-0/-home-user-degree-diameter/44b9d801-e3b0-5931-8a0d-00a602da11d2/scratchpad/bin/haar_big
R=/home/user/degree-diameter/research/squads/d16D10-r2
cd $R/c2 || exit 1
EVAL=$R/c2/OUT.txt.best UNCPRINT=1 THREADS=1 timeout 300 nice -n 10 $HB 16 10 0 1 1 /dev/null sl 61 10141 > eval1.out 2> eval1.log
echo "rc=$?" > eval1.rc
START=$R/c2/OUT.txt.best ORBIT="5 3 1" TMAX=0.15 TMIN=0.15 THREADS=1 timeout 660 nice -n 10 $HB 16 10 600 2 4 $R/c2/OUT2.txt sl 61 10141 > run2.out 2> run2.log
echo "rc=$?" > run2.rc
EVAL=$R/c2/OUT2.txt.best UNCPRINT=1 THREADS=1 timeout 300 nice -n 10 $HB 16 10 0 1 1 /dev/null sl 61 10141 > eval2.out 2> eval2.log
echo "rc=$?" > eval2.rc
echo WRAPPER_DONE > wrapper.done
