#!/bin/bash
# q5.sh: after q3 finishes: haarcheck_gen on the (13,11) push and the two D = 12 graphs at the 20-billion cap
cd "$(dirname "$0")"; export CTH=${CTH:-2}
for f in runs/d13D11_sl_563_19_orb3-4-1_s1.out runs/d12D12_psl_503_157_orb3-4-0_s1.out runs/d13D12_psl_307_691_orb3-4-1_s1.out; do
  echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q5 DONE $(date -u +%T)"
