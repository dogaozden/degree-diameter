#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/c2
for cfg in "nm180_c30_b31 auts_c30 2" "nm180_c30_b31 auts_c30 3" "nm180_c3xs3_b5_14 auts_c3s3 2" "nm180_c3xs3_b5_14 auts_c3s3 3" "nm180_c3xs3_b5_14 auts_c3s3 4"; do
  set -- $cfg
  timeout 500 nice -n 10 python3 eqred.py ../shared/seeds/$1.edges out/$2.json $3 out/eq_$1_h$3 > out/eq_$1_h$3.log 2>&1
done
echo ALLDONE > out/eq_chain.done
