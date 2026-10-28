#!/bin/bash
# c11: score each nonlinear rule on the p=5 grid (q in 13,17,19,23; m primes = 1 mod 3 up to 43)
D=/home/user/degree-diameter/research/squads/thmfam-r2/c11
T=/home/user/degree-diameter/research/theorems/haar_families
for R in lin sq cube absa sgn mod3 par tri inv cubic sqa0 sgna0 mixc ab; do
  OUT=$(nice -n 10 timeout 900 python3 $T/cover_score.py --p 5 --rule $R --qs 13,17,19,23 --ms 7,13,19,31,37,43 --gen "python3 $D/gen_nl.py {p} {q} {m} $R" 2>&1 | grep SUMMARY)
  echo "$R $OUT"
done
