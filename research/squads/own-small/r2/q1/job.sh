#!/bin/bash
# own-small r2 card q1: one gated job (run as: $T/slot.sh 900 bash job.sh). Everything stays in this folder.
cd /home/user/degree-diameter/research/squads/own-small/r2/q1 || exit 1
gcc -O2 -march=native -o salift4 salift4.c -lm || exit 1
python3 -I driver.py
