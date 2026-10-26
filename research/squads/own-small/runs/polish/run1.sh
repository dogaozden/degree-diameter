#!/bin/bash
cd /home/user/degree-diameter/research/squads/own-small
D=11 tools/bin/polish 8 runs/d11/g81.txt 5 runs/d11/push5_2.sol.best runs/polish/d11_n1296_g81_5.sol > runs/polish/d11_n1296.log 2>&1 &
D=10 tools/bin/polish 6 runs/gtxt/g68.txt 1 r2/k4/runs/C2_N68_g1.sol.best runs/polish/d10_n816_g68_1.sol > runs/polish/d10_n816.log 2>&1 &
D=10 tools/bin/polish 5 runs/gtxt/g82.txt 2 r2/k2/push/r3_N82_g2.sol.best runs/polish/d10_n820_g82_2.sol > runs/polish/d10_n820.log 2>&1 &
wait
D=10 tools/bin/polish 7 runs/gtxt/g58.txt 2 r2/k6/runs/N58_g2_s1.sol.best runs/polish/d10_n812_g58_2.sol > runs/polish/d10_n812.log 2>&1
echo DONE > runs/polish/done1
