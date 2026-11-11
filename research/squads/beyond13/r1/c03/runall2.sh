#!/bin/bash
cd /home/user/degree-diameter/research/squads/beyond13/r1/c03
for t in x13_sl_5_ x5_sl_7_ x9_psl_7_ x26_psl_5_; do
  nice -n 10 ./ex tables/$t.bin 13 1 > runs/D13_$t.out 2>&1
done
echo DONE > runs/runall2.done
