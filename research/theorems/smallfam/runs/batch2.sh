#!/bin/sh
# squares group p = 113 at (4,10) (12,656 vertices > 12,416), 2 threads
cd "$(dirname "$0")/.."
nice -n 5 python3 squares.py 4 10 113 --threads 2 > runs/squares_d4D10_p113.txt 2>&1
