#!/bin/bash
# All B2 heavy work in ONE gated process (one slot): (1) checker vs build_haar2 on random test solutions,
# (2) haar_sym solutions, (3) the same comparison on them plus corrupted copies.
B=/home/user/degree-diameter/research/squads/d11D10-r1/B2
H=/home/user/degree-diameter/research/structured/haar_sym
F=/home/user/degree-diameter/research/frontier/build_haar2.py
cd $B
run_pair() {   # run_pair FILE: checker and build_haar2 on one solution file
  b=${1%.txt}
  timeout 300 ./haarcheck_pq "$1" > "$b.pq.out" 2>&1
  timeout 600 python3 "$F" "$1" > "$b.b2.out" 2>&1
  echo "done $1" >> b2_all.progress
}
for f in tests/r_*.txt; do run_pair "$f"; done
echo "random tests finished" >> b2_all.progress
ORBIT="3 3 2" timeout 150 $H 11 7 40 1 8 d11D10_sl_9_7_orb3_B2test_s1.txt sl 9 7 > run1.log 2>&1
timeout 150 $H 11 6 40 2 8 d11D10_psl_25_1_orb1_B2test_s2.txt psl 25 1 > run2.log 2>&1
timeout 150 $H 11 8 40 3 8 d11D10_sl_32_1_orb1_B2test_s3.txt sl 32 1 > run3.log 2>&1
echo "haar_sym runs finished" >> b2_all.progress
sed '1s/^11 7 /11 1 /' d11D10_sl_9_7_orb3_B2test_s1.txt > tests/corrupt_D1_sl_9_7.txt
for f in d11D10_sl_9_7_orb3_B2test_s1.txt d11D10_psl_25_1_orb1_B2test_s2.txt d11D10_sl_32_1_orb1_B2test_s3.txt tests/corrupt_D1_sl_9_7.txt; do
  [ -s "$f" ] && run_pair "$f" || echo "missing $f" >> b2_all.progress
done
echo B2_ALL_DONE >> b2_all.progress
