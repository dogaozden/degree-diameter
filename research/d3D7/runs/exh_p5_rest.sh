#!/bin/bash
# finish the 5+5 sweep: order 20 for the bases not done by runs/exh_p5_17_21.out, and order 21; 4 jobs in parallel
cd "$(dirname "$0")/.."
job() { out=$1; N=$2; shift 2; : > $out; for b in "$@"; do echo "BASE bases/p5/$b.txt" >> $out; AUT=groups/a$N.txt ./bin/liftx bases/p5/$b.txt groups/g$N.txt 7 >> $out; done; echo DONE >> $out; }
job runs/exh_p5_N20_a.out 20 b5_14 b5_2 b5_3 &
job runs/exh_p5_N20_b.out 20 b5_4 b5_5 b5_6 &
job runs/exh_p5_N20_c.out 20 b5_7 b5_8 b5_9 &
job runs/exh_p5_N21.out 21 b5_0 b5_1 b5_2 b5_3 b5_4 b5_5 b5_6 b5_7 b5_8 b5_9 b5_10 b5_11 b5_12 b5_13 b5_14 &
wait
