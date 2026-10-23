#!/bin/bash
# Campaign 1 (voltage-lifts job): small cells, lifts over enumerated 2..12-vertex bases and structured bases.
# Each run_cell call has its own budget; every lift search has its own time limit (--secs).
cd "$(dirname "$0")"
P=bases/poly
W=${W:-3}
run() { python3 run_cell.py --workers $W --stop-on-solve "$@"; }
run --delta 4 --D 7 --orders 842:900 --hs 1,2,3,4,5,6 --secs 30 --maxbases 6 --maxgroups 5 --budget 2400 --tag c1_d4D7 --extra-bases $P/gq3.txt,$P/pg3.txt,$P/k44.txt
run --delta 3 --D 8 --orders 258:300 --hs 1,2,3,4,5,6,7 --secs 20 --maxbases 6 --maxgroups 5 --budget 1800 --tag c1_d3D8 --extra-bases $P/heawood.txt,$P/moebius_kantor.txt,$P/pappus.txt,$P/desargues.txt,$P/tutte8.txt
run --delta 3 --D 9 --orders 508:560 --hs 1,2,3,4,5,6,7 --secs 20 --maxbases 6 --maxgroups 5 --budget 1800 --tag c1_d3D9 --extra-bases $P/heawood.txt,$P/moebius_kantor.txt,$P/pappus.txt,$P/desargues.txt,$P/tutte8.txt
run --delta 3 --D 10 --orders 802:900 --hs 1,2,3,4,5,6,7 --secs 20 --maxbases 6 --maxgroups 5 --budget 1800 --tag c1_d3D10 --extra-bases $P/heawood.txt,$P/moebius_kantor.txt,$P/pappus.txt,$P/desargues.txt,$P/tutte8.txt,$P/gh2.txt
run --delta 6 --D 5 --orders 686:720 --hs 1,2,3,4,5,6 --secs 30 --maxbases 6 --maxgroups 5 --budget 2400 --tag c1_d6D5 --extra-bases $P/pg5.txt
run --delta 4 --D 8 --orders 2186:2300 --hs 1,2,3,4,5,6 --secs 40 --maxbases 5 --maxgroups 5 --budget 2400 --tag c1_d4D8 --extra-bases $P/gq3.txt,$P/pg3.txt,$P/gh2_j1_allfree.txt
run --delta 5 --D 7 --orders 3112:3250 --hs 1,2,3,4,5 --secs 40 --maxbases 5 --maxgroups 5 --budget 2400 --tag c1_d5D7
run --delta 4 --D 9 --orders 4972:5200 --hs 1,2,3,4,5,6 --secs 40 --maxbases 5 --maxgroups 5 --budget 2400 --tag c1_d4D9 --extra-bases $P/gq3.txt,$P/gh2_j1_allfree.txt
run --delta 5 --D 8 --orders 9236:9600 --hs 1,2,3,4,5 --secs 60 --maxbases 4 --maxgroups 5 --budget 2400 --tag c1_d5D8 --extra-bases $P/gh3_j1_allfree.txt
run --delta 4 --D 10 --orders 11750:12200 --hs 1,2,3,4,5,6 --secs 60 --maxbases 4 --maxgroups 5 --budget 2400 --tag c1_d4D10
run --delta 5 --D 9 --orders 27938:28600 --hs 1,2,3,4,5 --secs 90 --maxbases 4 --maxgroups 4 --budget 2400 --tag c1_d5D9
run --delta 5 --D 10 --orders 90070:92000 --hs 1,2,3,4,5 --secs 120 --maxbases 3 --maxgroups 4 --budget 2400 --tag c1_d5D10
