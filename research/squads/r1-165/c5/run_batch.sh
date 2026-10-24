#!/bin/bash
# usage: run_batch.sh SECONDS SEED  -- anneals every (base, group) pair, one process at a time.
# Output lines: base, group, n, m, best base-cost, full cost (= n * base cost), iterations, voltages.
# The controller edge list of the best assignment goes to /tmp/claude-0/c5/out/<base>_<group>_s<seed>.edges
S=${1:-8}; SEED=${2:-1}
T=/tmp/claude-0/c5/tables; BIN=/tmp/claude-0/c5/ctrl_lift; OUT=/tmp/claude-0/c5/out
mkdir -p $OUT
run() { # base group-file
  local line; line=$($BIN $T/$2.txt $1 $S $SEED $OUT/$1_$2_s$SEED.edges 4.0 2>&1)
  local n=$(echo "$line" | sed -n 's/.* n=\([0-9]*\) .*/\1/p')
  local c=$(echo "$line" | sed -n 's/.*best_cost=\([0-9]*\).*/\1/p')
  echo "$1 $2 n=$n m=$(echo "$line" | sed -n 's/.* m=\([0-9]*\) .*/\1/p') base_cost=$c full_cost=$((c*n)) $(echo "$line" | sed -n 's/.*iters=\([0-9]*\).*/iters=\1/p') $(echo "$line" | sed -n 's/.*volt=//p')"
}
for g in cyc_16 cyc_4_x_cyc_4 cyc_2_x_cyc_8 q8xz2 dih_4_x_cyc_2 meta_4_4_3 meta_8_2_3 meta_8_2_5; do run k44 $g; done
for g in cyc_17 cyc_18 meta_9_2_8 meta_3_6_2 cyc_20 meta_5_4_2 dih_10; do run k44 $g; done
for g in cyc_21 meta_7_3_2 cyc_22 dih_11 cyc_23 cyc_24 sl23; do run k33m $g; done
