#!/bin/bash
# c6c-h12: full A-root scans of the three order-12 families in PGL(2,193), one process at a time, nice -n 10,
# resumable (scanA skips classes already in the output). Usage of exh12: q psl g(4) s(4) DEG MODE args.
cd /home/user/degree-diameter/research/squads/handsoff-108/c6c-h12
E=./exh12
nice -n 10 timeout 3000 $E 193 0 0 1 192 0 81 1 112 1 10 scanA all out/A4_scanA.tsv 2>> out/A4_scanA.log
echo "A4 scanA rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
nice -n 10 timeout 3000 $E 193 0 85 0 0 1 0 1 5 0 10 scanA all out/D6nsq_scanA.tsv 2>> out/D6nsq_scanA.log
echo "D6nsq scanA rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
nice -n 10 timeout 4000 $E 193 0 85 0 0 1 0 1 2 0 10 scanA all out/D6sq_scanA.tsv 2>> out/D6sq_scanA.log
echo "D6sq scanA rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
echo "all scanA done $(date -u +%H:%M:%S)" >> out/progress.log
