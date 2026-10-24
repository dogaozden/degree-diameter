#!/bin/bash
# Campaign 1 (voltage-lifts job): the small cells. Per cell:
#  (a) "rich": Haar graphs and 2+2 / 3+3 bases over cyclic, metacyclic, matrix x cyclic and products of two non-abelian
#      groups; every (base, group) screened by 150 random voltage assignments, the best 8 per order annealed;
#  (b) "wide": every base on up to 2h = 12 vertices (enumerated) plus structured bases, generic group list.
# Each run_cell call has its own wall-clock budget; every lift search has its own time limit (--secs).
cd "$(dirname "$0")"
P=bases/poly
W=${W:-3}
run() { python3 run_cell.py --workers $W --stop-on-solve "$@"; }
cell() {  # delta D lo hi secs extra-bases
  run --delta $1 --D $2 --orders $3:$4 --hs 1,2,3 --rich --screen 150 --top 8 --maxbases 3 --maxgroups 40 --secs $5 --budget 1200 --tag c1r_d$1D$2
  run --delta $1 --D $2 --orders $3:$4 --hs 1,2,3,4,5,6 --secs $5 --maxbases 5 --maxgroups 4 --budget 900 --tag c1w_d$1D$2 ${6:+--extra-bases $6}
}
cell 3 8 258 290 20 $P/heawood.txt,$P/moebius_kantor.txt,$P/pappus.txt,$P/desargues.txt,$P/tutte8.txt
cell 3 9 508 540 20 $P/heawood.txt,$P/moebius_kantor.txt,$P/pappus.txt,$P/desargues.txt,$P/tutte8.txt
cell 3 10 802 890 20 $P/heawood.txt,$P/moebius_kantor.txt,$P/pappus.txt,$P/desargues.txt,$P/tutte8.txt
cell 6 5 686 720 30 $P/pg5.txt
cell 4 8 2186 2260 40 $P/gq3.txt,$P/pg3.txt,$P/gh2_j1_allfree.txt
cell 5 7 3112 3200 40
cell 4 9 4972 5100 45 $P/gq3.txt,$P/gh2_j1_allfree.txt
cell 5 8 9236 9500 60 $P/gh3_j1_allfree.txt
cell 4 10 11750 12000 60
cell 5 9 27938 28400 90
cell 5 10 90070 91000 120
