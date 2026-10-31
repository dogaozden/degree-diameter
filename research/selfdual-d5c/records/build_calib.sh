#!/bin/bash
# build_calib.sh: rebuild the two calibration graphs of selfdual-d5c from their formulas (independent builder, no
# GAP) and print their sha256; compare with README.md here.  Not records: both are below our (12,5) and (13,5) values.
cd "$(dirname "$0")"
B=../src/build_fsd_haar.py
python3 $B meta 97 36 6 1 "0,0 0,15 53,10 86,5 14,2 68,13 53,32 89,19 26,15 58,0 31,16 65,35" calib_d12D5_n6984_c97c36.edges
python3 $B meta 251 20 32 1 "0,0 79,10 4,10 5,19 160,11 68,12 154,8 44,13 124,17 34,1 205,9 29,7 237,3" calib_d13D5_n10040_c251c20.edges
sha256sum calib_d12D5_n6984_c97c36.edges calib_d13D5_n10040_c251c20.edges
