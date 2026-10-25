#!/bin/bash
# sequential batch of warm-started and one scratch orbclq run per subgroup class (one heavy process at a time)
cd /home/user/degree-diameter/research/squads/d14D7-r5/c6
for spec in "17 60 1 warm" "17 60 1 scratch" "15 60 1 warm" "12 60 1 warm" "9 60 1 warm" "11 60 1 warm" "7 60 1 warm" "3 60 1 warm"; do
  python3 runs.py $spec
done
echo ALLDONE
