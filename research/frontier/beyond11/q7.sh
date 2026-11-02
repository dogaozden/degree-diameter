#!/bin/bash
# q7.sh: the small checks left from q3 (q3's loop was stopped while its (14,11) check kept running)
cd "$(dirname "$0")"; export CTH=${CTH:-2}
for f in runs/d10D11_sl_613_1_orb3-3-1_d13.out runs/d9D11_sl_223_7_orb3-3-0_d08.out runs/d7D11_sl_53_37_orb3-2-1_d09.out runs/d11D11_sl_317_19_orb3-3-2_d01.out; do
  echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q7 DONE $(date -u +%T)"
