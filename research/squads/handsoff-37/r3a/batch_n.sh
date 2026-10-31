#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLM_DONE' out/batch_m.log)" -ge 1 ]; do sleep 3; done
./batch.sh cfg_n.txt
echo ALLN_DONE
