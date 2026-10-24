#!/bin/sh
# (4,9): every Z_p x| Z_k (p prime, 5 <= k <= p) with N = 2486..2900, exhaustive in normal form
cd "$(dirname "$0")/.."
nice -n 5 python3 frob_scan.py 4 9 2486 2900 --kmin 5 --threads 2 --maxsets 3e7 > runs/frob_d4D9.txt 2>&1
