#!/bin/bash
# runs the A-root scan of every class of K and then C, one process at a time, nice -n 10, resumable (scanA skips done ids)
cd /home/user/degree-diameter/research/squads/handsoff-108/c6b-exhaust
nice -n 10 timeout 6000 ./exh 229 1 1 1 1 27 1 0 26 228 scanA out/K_scanA.tsv 2>> out/K_scanA.log
echo "K scanA rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
nice -n 10 timeout 6000 ./exh 181 0 1 0 0 42 0 1 2 0 scanA out/C_scanA.tsv 2>> out/C_scanA.log
echo "C scanA rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
echo "all scanA done $(date -u +%H:%M:%S)" >> out/progress.log
