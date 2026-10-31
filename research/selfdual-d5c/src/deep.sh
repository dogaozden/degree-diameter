#!/bin/bash
# deep.sh K THR N SECS: deep tabu runs (SECS on the best record and type of each screened group, STALL 2000, seed 11)
# on the N lowest groups from deep_pick.py with best <= THR; one line each in logs/K$K/runs.txt (tag *_deep).
KK=$1; SS=$4
R0="$(cd "$(dirname "$0")/.." && pwd)"
python3 $R0/src/deep_pick.py $1 $2 | head -$3 | while read -r b kind rest; do
    set -- $kind $rest; nargs=$#; rec=${@: -2:1}; f=${@: -1}; gargs=${@:1:$((nargs-2))}
    K=$KK REC=$rec TYPES=$f SECS=$SS MAXSOL=1 SEED=11 TAG=deep NICE=0 $R0/src/run1.sh $gargs
done
