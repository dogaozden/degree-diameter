#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until [ "$(grep -c '^ALLN_DONE' out/batch_n.log)" -ge 1 ]; do sleep 3; done
./batch.sh cfg_o.txt
echo ALLO_DONE
