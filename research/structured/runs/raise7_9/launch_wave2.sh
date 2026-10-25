#!/bin/bash
# waits for wave 1 (5400 s searches) to finish, then starts wave 2 (ORBW=3, seed 2, 3600 s each)
cd "$(dirname "$0")/../../../.."
while [ "$(ps aux | grep -c '[h]aar_sym')" -gt 0 ]; do sleep 30; done
for n in psl17_97 sl17_49 psl41_7 psl13_217; do
  OMP_NUM_THREADS=1 THREADS=1 nohup nice -n 5 bash tools/orbq.sh runs/raise7_9/j2_$n.jobs runs/raise7_9 > runs/raise7_9/q2_$n.out 2>&1 &
done
wait
