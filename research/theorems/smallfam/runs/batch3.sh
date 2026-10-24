#!/bin/sh
# F_q x| C_k (q a prime power) Haar scans at (4,8) and (4,9), 1 thread
cd "$(dirname "$0")/.."
nice -n 5 python3 affq.py 4 8 1093 1700 --threads 1 --maxsets 3e7 > runs/affq_d4D8.txt 2>&1
nice -n 5 python3 affq.py 4 9 2486 4100 --threads 1 --maxsets 3e7 > runs/affq_d4D9.txt 2>&1
