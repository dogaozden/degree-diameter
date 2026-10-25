#!/bin/bash
# B3: formal identities of non-backtracking walks up to length 5 (3 random generators each), k = 10 and k = 5 orbits
cd /home/user/degree-diameter/research/squads/d11D10-r2/B3
python3 ident_walks.py k10 3 5 1 > ident_k10_L5.log 2>&1
python3 ident_walks.py k5 3 5 1 > ident_k5_L5.log 2>&1
echo done > ident_done.flag
