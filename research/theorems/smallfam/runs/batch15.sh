#!/bin/sh
# squad r1 follow-up: longer annealing on the best (4,9) and (4,8) leads (haar_gen3)
cd "$(dirname "$0")/.."
H=/tmp/claude-0/-home-user-degree-diameter/2c3fb1ba-9359-5c52-a9c4-6d81a7db2df8/scratchpad/haar_gen3
for s in 1 2 3; do
  THREADS=1 nice -n 5 $H 4 9 600 $s 8 runs/psl8x5_d4D9_s$s.txt psl 8 5 2>&1 | tail -1 >> runs/followup_r1.txt
  THREADS=1 nice -n 5 $H 4 8 400 $s 8 runs/psl7x7_d4D8_s$s.txt psl 7 7 2>&1 | tail -1 >> runs/followup_r1.txt
done
