#!/bin/bash
# tip.sh: rerun dmfast_hub from the OUT of a stalled coset-0 run (PTARG=1.0 TEMP0=0.5 TEMP1=0.05 SWAPP=0.05), two seeds
set -u
cd "$(dirname "$0")"
FREE="$(cat k7.sol.free)"
for SD in 1 2; do
  echo "== seed $SD: dmfast_hub from b_k7c8.sol"
  FREE="$FREE" RELAX=1 PATCH=1 PTARG=1.0 IN=b_k7c8.sol OUT="c_k7_s$SD.sol" BASE=gq/gq_q7.bin NPOLY=4 ITERS=3000000 TEMP0=0.5 TEMP1=0.05 SWAPP=0.05 SEED=$SD timeout 900 nice -n 10 ./dmfast_hub 7 2>&1 | tail -1
  [ -f "c_k7_s$SD.sol" ] || { echo "no OUT written"; continue; }
  python3 sol2lift2.py "c_k7_s$SD.sol" /dev/null >/dev/null 2>&1 || true
  echo "== seed $SD: hub graph + exact cost"
  FREE="$FREE" ITERS=0 HGIT=3000000 SEED=$SD timeout 900 nice -n 10 ./dmhub gq/gq_q7.bin "c_k7_s$SD.sol" "final_k7_s$SD" | grep -E 'final cost'
  ./apsp "final_k7_s$SD.edges" 10 5 && ./apsp "final_k7_s$SD.edges" 10 5 | grep -q 'RESULT VALID' && { echo "VALID at seed $SD"; break; }
done
echo TIP_DONE
