#!/bin/bash
# pipeline.sh (card c3): full-graph k-fixed tabu (pov_init, ADDFREE=0) started from
#  (a) the 198-point set best_c3_198.txt, and
#  (b) each 513-structure tabu set t_sS.txt (vertex ids) mapped to H(8) ids and greedily extended (ext.py).
cd /home/user/degree-diameter/research/squads/d10D7-r5/c3
H=/home/user/degree-diameter/research/d10D7/hex/hex_q8.bin
POV_INIT=$PWD/best_c3_198.txt timeout 200 nice -n 10 ./pov_init $H 21 90 pov_f198.txt 7 10 200000 5 1000000000000 0 > pov_f198.log 2>&1
for s in "$@"; do
  python3 -I tohex.py t_s$s.txt t_s${s}_hex.txt
  python3 -I ext.py t_s${s}_hex.txt ext_s$s.txt
  POV_INIT=$PWD/ext_s$s.txt timeout 200 nice -n 10 ./pov_init $H 1$s 60 pov_e$s.txt 7 10 200000 5 1000000000000 0 > pov_e$s.log 2>&1
done
echo pipeline-done
