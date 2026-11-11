#!/bin/bash
# sequential exhaustive D=13 search (S = {e,x,y}), first valid pair per group
cd /home/user/degree-diameter/research/squads/beyond13/r1/c03
for t in x4_perm_A6_ x2_perm_S6_ x12_sl_5_ x13_sl_5_ x12_perm_S5_ x24_psl_5_ x26_psl_5_ x4_pgl_7_ x4_sl_7_ x8_psl_7_ x9_psl_7_ x2_psl_11_ x5_sl_7_; do
  nice -n 10 ./ex tables/$t.bin 13 1 > runs/D13_$t.out 2>&1
done
echo DONE > runs/runall.done
