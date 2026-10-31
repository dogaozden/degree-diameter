#!/bin/bash
# chain_front.sh: after chain_deep.sh ends, K = 13 ladder runs between the solved 5,020 and the target (60 s per type)
R0="$(cd "$(dirname "$0")/.." && pwd)"
while pgrep -x chain_deep.sh > /dev/null; do sleep 30; done
for g in "131 40 42 1" "271 20 27 1"; do
    K=13 TYPES=1,3 SHUFFLE=1 STOPFIRST=1 SECS=60 TBUDGET=900 MAXSOL=1 SEED=1 TAG=lad NICE=0 $R0/src/run1.sh meta $g
done
