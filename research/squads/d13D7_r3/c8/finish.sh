#!/bin/bash
# usage: finish.sh MODEL_FILE  -> converts a fibre-model state to point indices and checks it with oppcheck
set -e
cd /home/user/degree-diameter/research/squads/d13D7_r3/c8
python3 fibconv.py model2idx "$1" "$1.idx" > /dev/null
/home/user/degree-diameter/research/d13D7/tools/oppcheck /home/user/degree-diameter/research/d13D7/hex/hex_q11.bin P "$1.idx"
