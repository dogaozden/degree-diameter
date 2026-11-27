#!/bin/bash
# qb5.sh (job beyond-d11b): replaces qb4.sh (no (15,11) push: the checks need the time). Waits for the (16,11) check,
# then haarcheck_gen on (15,11) and (14,12) (new cells), then (12,12) and (13,12) (raises). One ~11 GB check at a time.
cd "$(dirname "$0")"; export CTH=${CTH:-4}
while pgrep -f "haarcheck_gen runs/d16D11" >/dev/null; do sleep 10; done
echo "$(date -u +%T) (16,11) check finished: $(grep -hE '^VALID|^INVALID' runs/d16D11_psl_449_331_orb3-5-1_s1.gen.txt)"
for s in d15D11_sl_617_61_orb3-5-0_s1 d14D12_psl_241_2143_orb3-4-2_s1 d12D12_psl_241_2143_orb3-4-0_s1 d13D12_psl_181_5059_orb3-4-1_s1; do
  echo "$(date -u +%T) check $s"; ./gen.sh runs/$s.out; done
echo "QB5 DONE $(date -u +%T)"
