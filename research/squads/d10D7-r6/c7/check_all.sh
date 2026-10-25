#!/bin/bash
# score every candidate set in this folder with the official checker
cd /home/user/degree-diameter/research/squads/d10D7-r6/c7
for f in "$@"; do
  printf '%s: ' "$f"
  timeout 300 nice -n 10 /home/user/degree-diameter/research/squads/d10D7-r4/tools/setcheck /home/user/degree-diameter/research/d10D7/hex/hex_q11.bin "$f" points opposite
done
