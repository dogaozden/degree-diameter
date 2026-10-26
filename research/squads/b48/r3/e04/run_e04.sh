#!/bin/bash
# e04: non-abelian nilpotent groups (Heisenberg x cyclic, dihedral 2-groups x cyclic) as Haar graphs at D = 8, via haar_tab.
T=/home/user/degree-diameter/research/squads/b48/tools
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd "$(dirname "$0")"
for spec in "heis 3 x cyc 41:h3_41" "heis 3 x cyc 42:h3_42" "heis 3 x cyc 43:h3_43" "heis 3 x cyc 44:h3_44" "heis 5 x cyc 9:h5_9" "dih 8 x cyc 69:d8_69" "dih 8 x cyc 71:d8_71" "dih 8 x cyc 75:d8_75" "dih 16 x cyc 35:d16_35" "dih 16 x cyc 37:d16_37"; do
  s="${spec%%:*}"; f="${spec##*:}"
  timeout 120 nice -n 10 python3 $T/groups.py "$s" $f.bin
  THREADS=1 timeout 120 nice -n 10 $B/haar_tab 4 8 8 1 8 $f.sol tab $f.bin 1 | grep RESULT
done
# best family member, longer run (seed 2)
THREADS=1 timeout 120 nice -n 10 $B/haar_tab 4 8 40 2 8 d16_35_b.sol tab d16_35.bin 1 | grep RESULT
