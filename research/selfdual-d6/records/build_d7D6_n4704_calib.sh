#!/bin/bash
# Calibration graph (not a record): (7,6) Haar graph of SL(2,7) x Z7, N = 2,352, 4,704 vertices, self-dual S.
# Rebuilt from the formula by build_sdhi.py (no shared code with sdhi.c), then checked by apsp at D = 6 and D = 5.
set -e
cd "$(dirname "$0")"
S='[1 3 5 2]|0 [5 3 5 6]|0 [0 5 4 3]|4 [4 5 4 0]|3 [0 4 5 4]|5 [3 4 5 0]|2 [0 6 1 0]|0'
python3 ../src/build_sdhi.py 6 "sl 7" "cyc 7" "$S" d7D6_n4704_calib_sl7xz7.edges
sha256sum d7D6_n4704_calib_sl7xz7.edges
gcc -O2 -w -o /tmp/apsp_sd6 ../../lifts/coordinator_check/apsp.c
/tmp/apsp_sd6 d7D6_n4704_calib_sl7xz7.edges 7 6 | tail -1
/tmp/apsp_sd6 d7D6_n4704_calib_sl7xz7.edges 7 5 | tail -1
