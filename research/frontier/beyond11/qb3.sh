#!/bin/bash
# qb3.sh (job beyond-d11b): replaces qb2.sh after its first check. Waits for the (16,11) check, then pushes (15,11) to a
# higher rung (search only), checks the best (15,11), then the other three finds. One 7.6-11.2 GB job at a time.
cd "$(dirname "$0")"; export CTH=${CTH:-4}
while pgrep -f "haarcheck_gen runs/d16D11" >/dev/null; do sleep 10; done
echo "$(date -u +%T) (16,11) check finished: $(grep -hE '^VALID|^INVALID' runs/d16D11_psl_449_331_orb3-5-1_s1.gen.txt)"
[ -f runs/d16D11_psl_449_331_orb3-5-1_s1.gen.txt ] && grep -q "^VALID" runs/d16D11_psl_449_331_orb3-5-1_s1.gen.txt && cp runs/d16D11_psl_449_331_orb3-5-1_s1.out sols/d16D11_psl_449_331_orb3-5-1_s1.txt
best=d15D11_sl_617_61_orb3-5-0_s1
NOCHECK=1 ./hq.sh 15 11 1500 1 4 sl 571 79 "3 5 0" 4
if grep -q "best=0 " runs/d15D11_sl_571_79_orb3-5-0_s1.log; then best=d15D11_sl_571_79_orb3-5-0_s1
else NOCHECK=1 ./hq.sh 15 11 900 1 4 sl 601 67 "3 5 0" 4
     grep -q "best=0 " runs/d15D11_sl_601_67_orb3-5-0_s1.log && best=d15D11_sl_601_67_orb3-5-0_s1; fi
echo "$(date -u +%T) (15,11) to check: $best"
for s in $best d14D12_psl_241_2143_orb3-4-2_s1 d12D12_psl_241_2143_orb3-4-0_s1 d13D12_psl_181_5059_orb3-4-1_s1; do
  echo "$(date -u +%T) check $s"; ./gen.sh runs/$s.out; done
echo "QB3 DONE $(date -u +%T)"
