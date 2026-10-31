#!/bin/bash
# two-step exhaustive best insertion from conder168 (n 168 -> 170 -> 172) then LNS 240 s at n = 172
cd /home/user/degree-diameter/research/squads/handsoff-37/c8
./insbest ../shared/seeds/conder168.edges out/q170.edges
./insbest out/q170.edges out/q172.edges
nice -n 10 ./lns 172 601 240 3 1.0 0.5 2 out/Q172 out/q172.edges 0.4 2>&1 | grep -E "DONE|best=" | tail -2
echo INS3DONE
