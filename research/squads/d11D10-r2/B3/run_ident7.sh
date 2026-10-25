#!/bin/bash
# B3: formal identities of non-backtracking walks up to length 7 (two random generators), k = 10 and k = 5 orbits
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
env -u THREADS ./ident7 k10 7 1 > ident7_k10_L7.log 2>&1
env -u THREADS ./ident7 k5 7 1 > ident7_k5_L7.log 2>&1
echo "=== done ident7 ===" >> ident7_k5_L7.log
