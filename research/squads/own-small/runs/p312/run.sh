#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small/runs/p312
D=12 ../../tools/bin/polish 4 /home/user/degree-diameter/research/squads/own-small/runs/q312/g296.txt 3 /home/user/degree-diameter/research/squads/own-small/runs/queue2/out/dirD1_33.sol.best pol2368.sol > pol2368.log 2>&1 &
START=/home/user/degree-diameter/research/squads/own-small/runs/queue2/out/dirD1_33.sol.best D=12 ../../tools/bin/salift_s 4 /home/user/degree-diameter/research/squads/own-small/runs/q312/g296.txt 3 31 150 3 0.3 r31.sol > r31.log 2>&1 &
D=12 ../../tools/bin/salift_s 4 /home/user/degree-diameter/research/squads/own-small/runs/q312/g296.txt 3 32 150 10 0.3 r32.sol > r32.log 2>&1 &
D=12 ../../tools/bin/salift_s 4 /home/user/degree-diameter/research/squads/own-small/runs/q312/g296.txt 3 33 150 10 0.3 r33.sol > r33.log 2>&1 &
wait; echo DONE > done
