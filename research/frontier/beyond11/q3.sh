#!/bin/bash
# q3.sh: haarcheck_gen on the round-2 finds, largest first (CTH threads each)
cd "$(dirname "$0")"; export CTH=${CTH:-2}
for f in runs/d14D11_sl_1009_7_orb3-4-2_s1.out runs/d11D11_sl_317_19_orb3-3-2_d01.out runs/d10D11_sl_613_1_orb3-3-1_d13.out \
         runs/d9D11_sl_223_7_orb3-3-0_d08.out runs/d8D11_psl_113_31_orb3-2-2_d09.out runs/d7D11_sl_53_37_orb3-2-1_d09.out; do
  echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q3 DONE $(date -u +%T)"
