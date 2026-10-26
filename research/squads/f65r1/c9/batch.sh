#!/bin/bash
cd /home/user/degree-diameter/research/squads/f65r1/c9
for t in D86_chein Dic43_chein D87_chein D89_chein D90_chein DxZ29_3_chein DxZ43_2_chein A4xZ15_chein; do
  timeout 200 nice -n 10 ./hloop tables/$t.tab 50 7 runs/$t 100 > runs/$t.log 2>&1
done
for t in DxZ43_2_grp; do
  [ -f tables/$t.tab ] || python3 mktables.py DxZ43_2 grp > /dev/null
  timeout 200 nice -n 10 ./hloop tables/$t.tab 50 7 runs/$t 100 > runs/$t.log 2>&1
done
echo done > runs/BATCH_DONE
