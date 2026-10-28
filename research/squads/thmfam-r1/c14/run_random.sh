#!/bin/bash
# random alpha-closed baseline: gen_random_orb.py q 0 2 SEED, psl, seeds 1-3, q 23-112 and 113-199
cd /home/user/degree-diameter/research/theorems/haar_families
T=/home/user/degree-diameter/research/squads/thmfam-r1/c14
for s in 1 2 3; do
  nice -n 10 timeout 900 python3 family_score.py --gen "python3 gen_random_orb.py {q} 0 2 $s" --group psl --qrange 23 112 --json > $T/rand_s${s}_23_112.json
  nice -n 10 timeout 900 python3 family_score.py --gen "python3 gen_random_orb.py {q} 0 2 $s" --group psl --qrange 113 199 --json > $T/rand_s${s}_113_199.json
done
echo ALLDONE > $T/random_done.flag
