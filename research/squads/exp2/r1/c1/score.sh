#!/bin/bash
# usage: score.sh SOL TAG  -- writes edges_TAG.txt and apsp_TAG.txt (Delta = 7, D = 7) in this folder
set -e
cd /home/user/degree-diameter/research/squads/exp2/r1/c1
./d7hex edges hex/hex_q5.bin "$1" "edges_$2.txt"
timeout 900 nice -n 10 ./apsp "edges_$2.txt" 7 7 | tee "apsp_$2.txt"
