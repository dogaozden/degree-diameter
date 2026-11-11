#!/bin/bash
cd /home/user/degree-diameter/research/frontier/raise_small
S=runs/V/d4D14_meta_3079_81_568_c15.txt
{ echo "== metacheck"; timeout 1200 python3 tools/metacheck.py $S; echo "== apsp"; python3 tools/meta2edges.py $S runs/V/d4D14_c15.edges && timeout 3000 bin/apsp runs/V/d4D14_c15.edges 4 14; echo "== apsp at D=13"; timeout 3000 bin/apsp runs/V/d4D14_c15.edges 4 13 | tail -1; } > runs/V/v15.out 2>&1
