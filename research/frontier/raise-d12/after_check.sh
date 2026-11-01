#!/bin/bash
# wait for the (15,12) haarcheck_gen run to finish, then start the (11,12) search (needs 2.9 GB)
C=/home/user/degree-diameter/research/frontier/runs/cloudcheck/d15D12_psl_197_3924_orb3-5-0_s1.gen.txt
until grep -q "^exit" $C; do sleep 15; done
cd /home/user/degree-diameter/research/frontier/raise-d12/runs
ORBIT="5 2 1" AFROB=1 THREADS=2 /home/user/bin/haar_bigq 11 12 5400 31 4 d11D12_psl_243_811_orb5-2-1_s31.out psl 243 811 > d11D12_psl_243_811_orb5-2-1_s31.log 2>&1
