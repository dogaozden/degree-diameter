#!/bin/bash
export THREADS=1
cd /home/user/degree-diameter/research/theorems/smallfam
timeout 900 nice -n 10 python3 named.py 4 8 "PcGroupCode(3732073212403969685562167,1372)" --threads 1 --outdir /home/user/degree-diameter/research/squads/r1-smallfam/c2
