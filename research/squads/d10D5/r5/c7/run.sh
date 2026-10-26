#!/bin/bash
# card c7: two best-flip variants, run one after another (one heavy process at a time), from ../r4/
cd /home/user/degree-diameter/research/squads/d10D5/r4
# variant a: plain BESTFLIP (all newly unmixed pairs), Metropolis FLIPT=0.8
FLIPS=1 BESTFLIP=1 FLIPT=0.8 KZ=12 REPAIRS=12 SECS=480 STEP=15 SIZE=70 SEED=1 timeout 1500 nice -n 10 python3 lns2.py ../r5/S5.sol ../r5/S5_c0.lift2.sol "1 6 5" ../r5/c7/a.sol > ../r5/c7/a.log 2>&1
# variant b: WSCORE=1 (unroutable newly unmixed pairs weighted 10x), FLIPT=0.5
WSCORE=1 FLIPS=1 BESTFLIP=1 FLIPT=0.5 KZ=12 REPAIRS=12 SECS=480 STEP=15 SIZE=70 SEED=2 timeout 1500 nice -n 10 python3 lns2.py ../r5/S5.sol ../r5/S5_c0.lift2.sol "1 6 5" ../r5/c7/b.sol > ../r5/c7/b.log 2>&1
echo DONE > /home/user/degree-diameter/research/squads/d10D5/r5/c7/done.flag
