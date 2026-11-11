#!/bin/bash
# c5c-scanC: full scan of coset family C = PGL(2,181), H = D5 nonsquare reflection, N = 592,956.
# Pass 1 (scanA): A-root uBA, uAA for every class (resumable). Pass 2 (scanB): uBB for classes with uBA+uAA <= 50,
# best first (C_scanA_best.tsv is that filtered, sorted list). One process at a time, nice -n 10.
cd /home/user/degree-diameter/research/squads/handsoff-108/c5c-scanC
if ! grep -q "^C scanA done" out/progress.log 2>/dev/null; then
  nice -n 10 timeout 7800 ./exh 181 0 1 0 0 42 0 1 2 0 scanA out/C_scanA.tsv 2>> out/C_scanA.log
  echo "C scanA rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
fi
awk '$1=="A" && $5+$6<=50' out/C_scanA.tsv | sort -k5,5n -k6,6n | awk '{print}' > out/C_scanA_best_unsorted.tsv
awk '{print $5+$6, $0}' out/C_scanA_best_unsorted.tsv | sort -n -s -k1,1 | cut -d' ' -f2- > out/C_scanA_best.tsv
echo "best list: $(wc -l < out/C_scanA_best.tsv) classes with uBA+uAA<=50 $(date -u +%H:%M:%S)" >> out/progress.log
nice -n 10 timeout 3600 ./exh 181 0 1 0 0 42 0 1 2 0 scanB out/C_scanB.tsv 50 out/C_scanA_best.tsv 2>> out/C_scanB.log
echo "C scanB rc=$? $(date -u +%H:%M:%S)" >> out/progress.log
echo "all done $(date -u +%H:%M:%S)" >> out/progress.log
