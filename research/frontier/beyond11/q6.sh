#!/bin/bash
# q6.sh: after the (11,12) check: haarcheck_gen on the round-3/4 finds that are still the best per cell
cd "$(dirname "$0")"; export CTH=${CTH:-2}
while pgrep -f "haarcheck_gen runs/d11D12_psl_223_1009" >/dev/null; do sleep 15; done
for f in runs/d10D12_psl_337_97_orb3-3-1_f12.out runs/d9D12_psl_241_79_orb3-3-0_e11.out runs/d8D12_psl_167_61_orb3-2-2_f10.out \
         runs/d7D12_psl_67_199_orb3-2-1_e09.out runs/d8D11_sl_283_1_orb3-2-2_e04.out runs/d6D11_sl_29_43_orb3-2-0_f02.out \
         runs/d5D11_sl_53_1_orb3-1-2_e01.out runs/d5D12_psl_53_7_orb3-1-2_e07.out runs/d6D12_psl_79_19_orb3-2-0_e08.out \
         runs/d4D11_psl_29_1_orb3-1-1_f13.out runs/d4D12_sl_17_7_orb3-1-1_f14.out; do
  echo "$(date -u +%T) check $f"; ./gen.sh $f; done
echo "Q6 DONE $(date -u +%T)"
