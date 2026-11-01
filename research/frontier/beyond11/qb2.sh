#!/bin/bash
# qb2.sh (job beyond-d11b): haarcheck_gen on the five ~30-billion-vertex finds, one at a time (~11.2 GB each), new cells first.
cd "$(dirname "$0")"; export CTH=${CTH:-4}
for s in d16D11_psl_449_331_orb3-5-1_s1 d15D11_sl_617_61_orb3-5-0_s1 d14D12_psl_241_2143_orb3-4-2_s1 \
         d12D12_psl_241_2143_orb3-4-0_s1 d13D12_psl_181_5059_orb3-4-1_s1; do
  echo "$(date -u +%T) check $s"; ./gen.sh runs/$s.out; done
echo "QB2 DONE $(date -u +%T)"
