#!/bin/bash
# Speed measurements for SPEEDUP.md. Run on an otherwise idle machine, one process at a time.
# usage: speed_bench.sh H3_BINARY HF_BINARY > out.txt
# 1. RANDSAMPLE identity: haar_gen3 vs haar_fast print the same cost quantiles (same random S, same costs).
# 2. BENCH: ms per evaluation, haar_gen3's evaluation code (FAST=0) vs wide rows (FAST=2), with the breakdown.
# 3. End-to-end: same seed, VCLOCK, MAXSTEPS; FAST=0 vs FAST=2 must print the same TRACE hash; wall time ratio.
# 4. haar_gen3 itself: evaluations per second in a 60 s run vs haar_fast FAST=2 (wall-clock schedule).
H3=$1; HF=$2
CELLS=(
"7 8|psl 17 18|3000|100000|0.0004"
"6 7|meta 279 15 7 1|20000|20000|0.003"
"8 9|sl 59 3|300|4000|0.01"
"7 10|sl 49 9|100|1500|0.03"
"8 10|sl 107 3|60|600|0.08"
"15 8|sl 101 8|30|150|0.3"
"10 8|psl 23 97|100|800|0.05"
"12 9|sl 127 8|10|40|1.2"
"10 10|sl 307 1|6|25|2.0"
)
for c in "${CELLS[@]}"; do
  IFS='|' read -r dD grp bench steps vclock <<< "$c"
  echo "=== $dD $grp"
  a=$(RANDSAMPLE=200 $H3 $dD 1 1 8 /dev/null $grp 2>/dev/null); b=$(RANDSAMPLE=200 $HF $dD 1 1 8 /dev/null $grp 2>/dev/null)
  [ "$a" == "$b" ] && echo "RANDSAMPLE identical: $a" || echo "RANDSAMPLE DIFFER: $a | $b"
  for f in 0 2; do FAST=$f BENCH=$bench $HF $dD 1 1 8 /dev/null $grp 2>/dev/null; done
  for f in 0 2; do echo "E2E FAST=$f $(TRACE=1 VCLOCK=$vclock MAXSTEPS=$steps FAST=$f $HF $dD 36000 1 8 /dev/null $grp 2>/dev/null | grep TRACE)"; done
  echo "H3 $( $H3 $dD 60 1 8 /dev/null $grp 2>/dev/null | grep RESULT)"
  echo "HF $( $HF $dD 60 1 8 /dev/null $grp 2>/dev/null | grep RESULT)"
done
