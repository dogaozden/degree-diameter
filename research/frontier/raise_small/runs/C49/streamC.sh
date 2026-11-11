#!/bin/bash
# director stream C: (4,9) quartic 2+2 joint lift over Z13 x|_2 Z96 (N=1248, n=4992 > 4,970), chained salift4
cd /home/user/degree-diameter/research/frontier/raise_small
BIN=salift4 DEG=4 tools/chain.sh 9 2 13 96 2 runs/C49/start1248.best 100 12 2000 runs/C49
