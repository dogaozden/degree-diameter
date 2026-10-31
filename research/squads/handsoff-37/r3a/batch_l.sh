#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^BATCH_DONE' out/batch_k.log)" -ge 1 ]; do sleep 3; done
./batch.sh cfg_l.txt
echo ALLL_DONE
