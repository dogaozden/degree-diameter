#!/bin/bash
# timing only (no build_haar2 above 2M vertices): checker on a ~40M-vertex random Haar graph over PSL(2,49) x Z_340
cd /home/user/degree-diameter/research/squads/d11D10-r1/B2
s=$(date +%s); timeout 280 ./haarcheck_pq tests/timing_psl49_n340.txt > timing.pq.out 2>&1; rc=$?
echo "rc=$rc secs=$(( $(date +%s) - s ))" >> b2_timing.progress
