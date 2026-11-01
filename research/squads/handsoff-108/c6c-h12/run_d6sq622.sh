#!/bin/bash
# c6c-h12: full A-root scan of the 6+2+2 partition of the D6 square family (the last partition of that family), resumable.
cd /home/user/degree-diameter/research/squads/handsoff-108/c6c-h12
nice -n 10 timeout 3300 ./exh12 193 0 85 0 0 1 0 1 2 0 10 scanA 6,2,2 out/D6sq_scanA.tsv 2>> out/D6sq_scanA.log
echo "D6sq 6,2,2 rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
