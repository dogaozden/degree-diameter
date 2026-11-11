#!/bin/bash
# q4.sh: haarcheck_gen on the (11,12) push and the round-3 finds (CTH threads)
cd "$(dirname "$0")"; export CTH=${CTH:-2}
for f in runs/d11D12_psl_223_1009_orb3-3-2_s2.out runs/d10D12_psl_239_271_orb3-3-1_e12.out runs/d9D12_psl_241_79_orb3-3-0_e11.out \
         runs/d8D12_sl_113_97_orb3-2-2_e10.out runs/d7D12_psl_67_199_orb3-2-1_e09.out runs/d8D11_sl_283_1_orb3-2-2_e04.out \
         runs/d5D11_sl_53_1_orb3-1-2_e01.out runs/d6D11_sl_53_7_orb3-2-0_e02.out runs/d5D12_psl_53_7_orb3-1-2_e07.out runs/d6D12_psl_79_19_orb3-2-0_e08.out; do
  echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q4 DONE $(date -u +%T)"
