#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small
D=11 tools/bin/polish 4 runs/q311/g170.txt 1 /home/user/degree-diameter/research/squads/own-small/runs/queue/out/dir2_79.sol.best runs/polish/d11_n1360_g170_1.sol > runs/polish/d11_n1360.log 2>&1 &
D=11 tools/bin/polish 4 runs/q311/g171.txt 1 /home/user/degree-diameter/research/squads/own-small/runs/queue/out/dir5_87.sol.best runs/polish/d11_n1368_g171_1.sol > runs/polish/d11_n1368.log 2>&1 &
D=12 tools/bin/polish 4 runs/q312/g291.txt 1 /home/user/degree-diameter/research/squads/own-small/runs/queue2/out/dirB0_41.sol.best runs/polish/d12_n2328_g291_1.sol > runs/polish/d12_n2328.log 2>&1 &
D=12 tools/bin/polish 4 runs/q312/g300.txt 13 /home/user/degree-diameter/research/squads/own-small/runs/queue/out/dirB2_107.sol.best runs/polish/d12_n2400_g300_13.sol > runs/polish/d12_n2400.log 2>&1 &
wait; echo DONE > runs/polish/done_final
