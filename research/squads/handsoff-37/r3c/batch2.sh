#!/bin/bash
# waits for batch1, then continues the best batch1 state of each open case, plus COMP tests at 170
cd /home/user/degree-diameter/research/squads/handsoff-37/r3c
while ! grep -q BATCH1_DONE out/runs.tsv; do sleep 10; done
export MODE=fbo BOWALK=1 STALL=1500 POOL=8 PP=60 FR=1 WCAP=16 TEN=4
best_state() {  # $1 = label prefix (e.g. b1_176C4); prints the state file of the lowest far
  for f in out/${1}_s*_best.edges; do
    far=$(../bin/score37 $f 2>/dev/null | sed -n 's/.*far=\([0-9]*\).*/\1/p')
    echo "$far $f"
  done | sort -n | head -1 | awk '{print $2}' | sed 's/_best.edges$/_best.state/'
}
for spec in "b1_176C4 C4 22" "b1_176C2C2 C2xC2 22" "b1_180C6 C6 15" "b1_180C5 C5 18" "b1_180C3 C3 30" "b1_180S3 S3 15"; do
  set -- $spec
  st=$(best_state $1)
  [ -n "$st" ] && INIT=$st ./run.sh c2_$1 $2 $3 501 90 >/dev/null
done
for S in 501 502; do COMP=100 ./run.sh c2comp170 C5 17 $S 90 >/dev/null; done
for S in 501 502; do ./run.sh c2pl170 C5 17 $S 90 >/dev/null; done
echo BATCH2_DONE >> out/runs.tsv
