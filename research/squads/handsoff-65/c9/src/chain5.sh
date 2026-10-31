#!/bin/sh
# after chain4: tabu 300 s from the best 704-vertex 2+2 vl solution (C11xQ16), then a second group (C4x(C11:C4))
cd /home/user/degree-diameter/research/squads/handsoff-65/c9
while kill -0 17205 2>/dev/null; do sleep 10; done
INIT=sol SECS=300 SEED=3 timeout 600 nice -n 10 ../shared/tabu runs/ms_MS2_2p2_176_26_5181.sol groups/sg_176_26.txt runs/tabu_176_26_s3.sol > runs/tabu_176_26_s3.out 2> runs/tabu_176_26_s3.err
INIT=sol SECS=300 SEED=4 timeout 600 nice -n 10 ../shared/tabu runs/ms_MS2_2p2_176_10_5103.sol groups/sg_176_10.txt runs/tabu_176_10_s4.sol > runs/tabu_176_10_s4.out 2> runs/tabu_176_10_s4.err
