#!/bin/bash
# Calibration (smaller m, to see whether cost 0 is reachable at all) and longer runs at the best m >= 62 candidates.
# usage: run_calib.sh  (expects tables in /tmp/claude-0/c5/tables and the ctrl_lift binary in /tmp/claude-0/c5)
T=/tmp/claude-0/c5/tables; BIN=/tmp/claude-0/c5/ctrl_lift; OUT=/tmp/claude-0/c5/out; mkdir -p $OUT
for k in 10 12 14; do [ -f $T/cyc_$k.txt ] || (cd /home/user/degree-diameter/research/theorems/squad165 && python3 dump_table.py "cyc $k" $T/cyc_$k.txt); done
for k in 14 16 18; do [ -f $T/cyc_$k.txt ] || (cd /home/user/degree-diameter/research/theorems/squad165 && python3 dump_table.py "cyc $k" $T/cyc_$k.txt); done
for spec in "k44 cyc_10 6 2" "k44 cyc_12 6 2" "k44 cyc_14 6 2" "k33m cyc_14 6 2" "k33m cyc_16 6 2" "k33m cyc_18 6 2"; do
  set -- $spec
  line=$($BIN $T/$2.txt $1 $3 $4 $OUT/$1_$2_s$4.edges 4.0 2>&1); echo "CALIB $1 $2 $line"
done
line=$($BIN $T/cyc_21.txt k33m 40 2 $OUT/k33m_cyc_21_s2.edges 4.0 2>&1); echo "LONG k33m cyc_21 $line"
line=$($BIN $T/meta_4_4_3.txt k44 40 2 $OUT/k44_meta443_s2.edges 4.0 2>&1); echo "LONG k44 meta_4_4_3 $line"
