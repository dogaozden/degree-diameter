#!/bin/bash
export THREADS=1
cd /home/user/degree-diameter/research/theorems/smallfam
timeout 900 nice -n 10 python3 named.py 4 8 "PcGroupCode(670367254001291709118534034953843781759,1500)" "PcGroupCode(441479163348293283161120977955983679,1500)" "PcGroupCode(204841060007963265828095,1250)" "PcGroupCode(446911499570852612291007474730270847,1500)" --threads 1 --outdir /home/user/degree-diameter/research/squads/r1-smallfam/c2
