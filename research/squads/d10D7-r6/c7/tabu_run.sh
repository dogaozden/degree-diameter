#!/bin/bash
# usage: tabu_run.sh INIT SEED SECONDS OUT   (potabu2 k-fixed tabu from a structured start, H(11) hexagon file)
cd /home/user/degree-diameter/research/squads/d10D7-r6/c7
timeout 1700 nice -n 10 ./potabu2 /home/user/degree-diameter/research/d10D7/hex/hex_q11.bin "$2" "$3" "$4" "$1" 2> "$4.log"
