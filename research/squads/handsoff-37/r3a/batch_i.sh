#!/bin/bash
cd /home/user/degree-diameter/research/squads/handsoff-37/r3a
until grep -q "^BATCH_DONE" out/batch_h.log && [ "$(grep -c '^BATCH_DONE' out/batch_h.log)" -ge 2 ]; do sleep 3; done
./batch.sh cfg_i.txt
echo ALLI_DONE
