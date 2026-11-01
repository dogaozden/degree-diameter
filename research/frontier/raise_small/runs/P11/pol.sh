#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
python3 tools/gtab.py runs/P11/g192.tab 48 4 5 2>/dev/null
D=11 timeout 3000 bin/polish 4 runs/P11/g192.tab 1 runs/P11/s192e.best runs/P11/p192.sol > runs/P11/pol.out 2>&1
if [ -f runs/P11/p192.sol ]; then python3 tools/sol2edges.py runs/P11/p192.sol 48 4 5 runs/P11/p192.edges; bin/apsp runs/P11/p192.edges 3 11 >> runs/P11/pol.out; fi
