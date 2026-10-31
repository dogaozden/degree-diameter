#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLL_DONE' out/batch_l.log)" -ge 1 ]; do sleep 3; done
./batch.sh cfg_m.txt
echo ALLM_DONE
