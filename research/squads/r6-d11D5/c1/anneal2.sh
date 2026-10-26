#!/bin/bash
# Two anneals, one at a time: best start of the best two patterns (path P6 = idx 7, theta = idx 15).
cd /home/user/degree-diameter/research/squads/r6-d11D5/c1
timeout 900 nice -n 10 env THREADS=1 SECS=500 SEED=1 T0=2 T1=0.15 PF=0.3 PH=0.7 OUT=/home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_p07.in OUT0=/home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_p07.0.in /tmp/po7 /home/user/degree-diameter/research/squads/r6-d11D5/c1/starts/p07.in > /home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_p07.log 2>&1
echo "p07 exit $?" >> /home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_status.txt
timeout 900 nice -n 10 env THREADS=1 SECS=500 SEED=1 T0=2 T1=0.15 PF=0.3 PH=0.7 OUT=/home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_p15.in OUT0=/home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_p15.0.in /tmp/po7 /home/user/degree-diameter/research/squads/r6-d11D5/c1/starts/p15.in > /home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_p15.log 2>&1
echo "p15 exit $?" >> /home/user/degree-diameter/research/squads/r6-d11D5/c1/anneal_status.txt
