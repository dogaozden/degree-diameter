#!/bin/bash
cd /home/user/degree-diameter/research/squads/d13D7_r4/c1
while kill -0 8859 2>/dev/null; do sleep 5; done
timeout 900 nice -n 10 python3 sweep.py blocks --dims 5,2 --seed 11 --cpu 300 --texact 3 --theur 4 --kmax 9000 --perdraw 3 --dmax 800 > work/blocks52.out 2>&1
timeout 900 nice -n 10 python3 sweep.py blocks --dims 4,3 --seed 12 --cpu 200 --texact 3 --theur 4 --kmax 9000 --perdraw 3 --dmax 800 > work/blocks43.out 2>&1
timeout 900 nice -n 10 python3 sweep.py blocks --dims 3,2,2 --seed 13 --cpu 200 --texact 3 --theur 4 --kmax 9000 --perdraw 3 --dmax 800 > work/blocks322.out 2>&1
timeout 900 nice -n 10 python3 sweep.py blocks --dims 6,1 --seed 14 --cpu 100 --texact 3 --theur 4 --kmax 9000 --perdraw 3 --dmax 800 > work/blocks61.out 2>&1
echo CHAIN_DONE
