#!/bin/bash
# B3: baseline for plain random S (no orbit structure), 40 samples, psl 243 x Z11
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
env -u THREADS RANDSAMPLE=40 LEVELS=3 /home/user/degree-diameter/research/structured/haar_sym 11 10 60 9 8 /dev/null psl 243 11
echo "=== done random40 ==="
