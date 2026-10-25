#!/bin/bash
# Reproducible tests of bcd (about 1 minute on 2 threads). Usage: bash run_tests.sh
# 1. random cyclic Haar graphs and random rotation-symmetric lifts, seeds 1..8: bcd lift, bcd explicit (with and
#    without automorphisms) and apsp.c must report the same diameter (or both disconnected);
# 2. a lift spec with one voltage changed must fail the automorphism check;
# 3. parts + merge + spot-check on a lift; WB=8 and WB=64 give identical certificates;
# 4. four Haar records as lifts of the dipole (SL/PSL x Z_n) are VALID at D and fail at D-1.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); ROOT=$HERE/../../../..; T=$(mktemp -d)
gcc -O3 -march=native -fopenmp -o $T/bcd $HERE/../bcd.c 2>/dev/null && gcc -O3 -march=native -fopenmp -DWB=8 -o $T/bcd8 $HERE/../bcd.c 2>/dev/null
gcc -O2 -o $T/apsp $ROOT/research/lifts/coordinator_check/apsp.c 2>/dev/null
fail=0; cd $T
for s in 1 2 3 4 5 6 7 8; do
  python3 $HERE/mk_lifts.py $s
  for t in haar rot; do
    a=$(./apsp $t.edges 6 40 | grep -o "diameter=[0-9]*\|disconnected" | head -1)
    b=$(./bcd lift $t.spec 6 40 --threads 2 2>/dev/null | grep -o "^diameter=[-0-9]*"); [ "$b" = "diameter=-1" ] && b=disconnected
    c=$(./bcd explicit $t.edges 6 40 --threads 2 2>/dev/null | grep -o "^diameter=[-0-9]*"); [ "$c" = "diameter=-1" ] && c=disconnected
    if [ "$a" != "$b" ] || [ "$a" != "$c" ]; then echo "FAIL seed $s $t: apsp $a, bcd lift $b, bcd explicit $c"; fail=1; fi
  done
  d=$(./bcd explicit rot.edges 6 40 --aut rot.aut --threads 2 2>/dev/null | grep -o "^diameter=[-0-9]*"); [ "$d" = "diameter=-1" ] && d=disconnected
  e=$(./apsp rot.edges 6 40 | grep -o "diameter=[0-9]*\|disconnected" | head -1)
  [ "$d" = "$e" ] || { echo "FAIL seed $s explicit+aut: $d vs $e"; fail=1; }
  ./bcd lift bad.spec 6 40 2>/dev/null | grep -q "automorphism check failed" || { echo "FAIL seed $s: bad automorphism accepted"; fail=1; }
done
python3 $HERE/mk_lifts.py 1
for i in 0 1 2; do ./bcd lift rot.spec 6 16 --part $i/3 --cert c$i.cert --reps reps.txt >/dev/null 2>&1; ./bcd8 lift rot.spec 6 16 --part $i/3 --cert w$i.cert >/dev/null 2>&1; cmp -s c$i.cert w$i.cert || { echo "FAIL WB=8 certificate differs"; fail=1; }; done
python3 $HERE/../bcd_merge.py reps.txt c0.cert c1.cert c2.cert | grep -q "RESULT VALID" || { echo "FAIL merge"; fail=1; }
python3 $HERE/../bcd_merge.py reps.txt c0.cert c2.cert >/dev/null 2>&1 && { echo "FAIL merge accepted a missing part"; fail=1; }
python3 $HERE/../bcd_spotcheck.py ./bcd lift rot.spec 6 16 c0.cert c1.cert c2.cert --sample 3 --threads 1 | grep -q "SPOTCHECK OK" || { echo "FAIL spotcheck"; fail=1; }
for f in d6D9_sl_17_13_orb3f0_s2 d7D9_psl_29_19_orb3_s1 d8D8_psl_17_49_orb3_s1 d9D8_psl_19_79_orb3_s1; do
  sol=$ROOT/research/frontier/sols/$f.txt; d=$(head -1 $sol | awk '{print $1}'); D=$(head -1 $sol | awk '{print $2}')
  python3 $HERE/../haar2lift.py $sol $f.spec >/dev/null
  ./bcd lift $f.spec $d $D --threads 2 2>/dev/null | grep -q "RESULT VALID" || { echo "FAIL $f not valid at D=$D"; fail=1; }
  ./bcd lift $f.spec $d $((D-1)) --threads 2 2>/dev/null | grep -q "RESULT INVALID" || { echo "FAIL $f valid at D-1"; fail=1; }
done
rm -rf $T
[ $fail = 0 ] && echo "ALL TESTS PASSED" || echo "SOME TESTS FAILED"
