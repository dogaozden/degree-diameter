#!/bin/bash
# b01 commands actually run (round 2). Paths: T = tools, B = scratchpad bin.
T=/home/user/degree-diameter/research/squads/b48/tools
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r2/b01
mkdir -p seeds
# 30 seeds on meta 91 12 25 (all valid, each ~0.1 s)
for s in $(seq 101 130); do
  THREADS=1 timeout 60 nice -n 10 $B/haar_fast 4 8 20 $s 8 seeds/m91_$s.txt meta 91 12 25 1 > seeds/m91_$s.log 2>&1
  grep -q "best=0" seeds/m91_$s.log && python3 /home/user/degree-diameter/research/frontier/build_haar2.py seeds/m91_$s.txt seeds/m91_$s.edges >/dev/null 2>&1
done
# damage per edge orbit at vertex 0, and validity
for f in seeds/*.edges; do THREADS=1 timeout 60 nice -n 10 $T/edgecrit $f 8 0 4; THREADS=1 timeout 60 nice -n 10 $T/score48 $f | tail -1; done
# metacyclic scan of all faithful Z_m x| Z_k of order 1092 (2 s each), list in scan/list.txt
python3 -c "
from math import gcd
N=1092
for k in range(2,N+1):
    if N%k: continue
    m=N//k
    if m<2: continue
    for r in range(2,m):
        if gcd(r,m)!=1 or pow(r,k,m)!=1: continue
        o=1; x=r
        while x!=1: x=x*r%m; o+=1
        if o==k: print(m,k,r)
" > scan/list.txt
while read m k r; do res=$(THREADS=1 timeout 20 nice -n 10 $B/haar_fast 4 8 2 3 8 scan/o_${m}_${k}_${r}.txt meta $m $k $r 1 2>&1 | grep RESULT | sed 's/.*best=//'); echo "$m $k $r best=$res"; done < scan/list.txt > scan/results.txt
# order-1092 abc group (F_4 x F_7 x F_13, Z_3) with haar_tab, and 40 s runs on cost-3 metacyclic groups
timeout 120 nice -n 10 python3 $T/abc.py build "3 2:3,7:3,13:3" abc1092.bin
THREADS=1 timeout 60 nice -n 10 $B/haar_tab 4 8 20 1 8 tab_s1.txt tab abc1092.bin 1
THREADS=1 timeout 60 nice -n 10 $B/haar_fast 4 8 40 11 8 c3_91_12_6.txt meta 91 12 6 1
THREADS=1 timeout 60 nice -n 10 $B/haar_fast 4 8 40 11 8 c3_91_12_20.txt meta 91 12 20 1
