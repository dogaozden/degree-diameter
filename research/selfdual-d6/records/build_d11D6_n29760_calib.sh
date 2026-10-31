#!/bin/bash
# Calibration graph (not a record): (11,6) Haar graph of PSL(2,31), N = 14,880, 29,760 vertices (plain S, haar_sd).
# Rebuilt from the solution file by research/frontier/build_haar2.py, then checked by apsp at D = 6 and D = 5.
set -e
cd "$(dirname "$0")"
python3 ../../frontier/build_haar2.py d11D6_n29760_calib_psl31.sol d11D6_n29760_calib_psl31.edges | tail -2
sha256sum d11D6_n29760_calib_psl31.edges
gcc -O2 -w -o /tmp/apsp_sd6 ../../lifts/coordinator_check/apsp.c
/tmp/apsp_sd6 d11D6_n29760_calib_psl31.edges 11 6 | tail -1
/tmp/apsp_sd6 d11D6_n29760_calib_psl31.edges 11 5 | tail -1
