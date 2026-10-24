#!/bin/bash
# pipeline.sh (card B3): three small pgl solutions from haar_sym, the cross-check batch, one large random instance.
cd "$(dirname "$0")" || exit 1
H=/home/user/degree-diameter/research/structured/haar_sym
env -u ORBIT -u THREADS $H 11 5 30 1 8 base/d11D5_pgl_13_1_orb0_plain_s1.txt pgl 13 1 > haar_t1.log 2>&1
env -u ORBIT -u THREADS $H 11 5 30 2 8 base/d11D5_pgl_7_12_orb0_plain_s2.txt pgl 7 12 > haar_t2.log 2>&1
env -u ORBIT -u THREADS $H 11 6 30 3 8 base/d11D6_pgl_11_20_orb0_plain_s3.txt pgl 11 20 > haar_t3.log 2>&1
./batch.sh > batch.log 2>&1
./big.sh > big.log 2>&1
echo "pipeline done rc=$?"
