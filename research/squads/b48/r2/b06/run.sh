#!/bin/bash
# b06 commands actually run (THREADS=1 nice; one process at a time)
T=/home/user/degree-diameter/research/squads/b48/tools
B=/tmp/claude-0/-home-user-degree-diameter/dc6fd85c-f533-550d-af33-040d4dcb67e6/scratchpad/bin
cd /home/user/degree-diameter/research/squads/b48/r2/b06
python3 enum_meta.py 1040 1091 > meta_list.txt
# 18 metacyclic groups, one per order (6 s each); then 5 abc groups (haar_tab 8 s)
while read N m k r o; do THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 6 1 8 screen/m_${m}_${k}_${r}.txt meta $m $k $r 1; done < pick2.txt
for g in g1 g2 g3 g4 g5; do THREADS=1 timeout 120 nice -n 10 $B/haar_tab 4 8 8 1 8 abc/${g}_sol.txt tab abc/$g.bin 1; done
# push the three best (25 s, seed 7)
for spec in "213 5 196" "211 5 107" "47 23 2"; do set -- $spec; THREADS=1 timeout 120 nice -n 10 $B/haar_fast 4 8 25 7 8 push/m_$1_$2_$3.txt meta $1 $2 $3 1; done
# near-miss states with lift (20 s, seed 3) and their far pairs / edge damage
for spec in "213:5:196" "211:5:107"; do n=$(echo $spec | tr : _); THREADS=1 QUIET=1 timeout 120 nice -n 10 $T/lift $T/bases/dipole4.txt meta:$spec 4 8 20 3 8 lift/s_$n.sol; done
$T/score48 lift/s_213_5_196.sol.edges; $T/edgecrit lift/s_213_5_196.sol.edges 8 0 4
