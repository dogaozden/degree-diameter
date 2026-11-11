#!/bin/bash
# Campaign 2 (voltage-lifts job): Haar graphs (and 2+2 bases) over groups with a matrix factor (SL/PSL/PGL(2,p) times
# cyclic or metacyclic), the family of the (4,7) record A5 x Z7. One worker; screened by 200 random assignments,
# best 3 per order annealed. Each run_cell call has a wall-clock budget, each search a time limit.
cd "$(dirname "$0")"
run() { python3 run_cell.py --workers 1 --stop-on-solve --rich --matrix-only --screen 200 --top 3 --maxbases 2 --maxgroups 400 "$@"; }
run --delta 4 --D 7 --orders 842:1100 --hs 1,2 --secs 60 --budget 1800 --tag c2_d4D7
run --delta 6 --D 5 --orders 686:780 --hs 1,2 --secs 60 --budget 1500 --tag c2_d6D5
run --delta 3 --D 8 --orders 258:300 --hs 1,2 --secs 30 --budget 900 --tag c2_d3D8
run --delta 3 --D 9 --orders 508:600 --hs 1,2 --secs 30 --budget 900 --tag c2_d3D9
run --delta 3 --D 10 --orders 802:1010 --hs 1,2 --secs 30 --budget 900 --tag c2_d3D10
run --delta 4 --D 8 --orders 2186:2400 --hs 1,2 --secs 60 --budget 1800 --tag c2_d4D8
run --delta 5 --D 7 --orders 3112:3400 --hs 1,2 --secs 60 --budget 1800 --tag c2_d5D7
run --delta 4 --D 9 --orders 4972:5300 --hs 1,2 --secs 60 --budget 1800 --tag c2_d4D9
run --delta 5 --D 8 --orders 9236:9800 --hs 1,2 --secs 90 --budget 1800 --tag c2_d5D8
run --delta 4 --D 10 --orders 11750:12400 --hs 1,2 --secs 90 --budget 1800 --tag c2_d4D10
run --delta 5 --D 9 --orders 27938:28600 --hs 1 --secs 120 --budget 1800 --tag c2_d5D9
run --delta 5 --D 10 --orders 90070:91200 --hs 1 --secs 180 --budget 2400 --tag c2_d5D10
