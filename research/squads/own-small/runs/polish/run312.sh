#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small
D=12 tools/bin/polish 4 runs/q312/g294.txt 16 /home/user/degree-diameter/research/squads/own-small/runs/queue/out/dirB1_106.sol.best runs/polish/d12_n2352_g294_16.sol > runs/polish/d12_n2352_g16.log 2>&1
D=12 tools/bin/polish 4 runs/q312/g294.txt 11 /home/user/degree-diameter/research/squads/own-small/runs/queue2/out/dirC_3.sol.best runs/polish/d12_n2352_g294_11.sol > runs/polish/d12_n2352_g11.log 2>&1
echo DONE > runs/polish/done312
