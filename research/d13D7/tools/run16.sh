#!/bin/bash
# run16.sh RFILE : (16,7) = 5 copies of H(13) + 4|R| from a set R of pairwise opposite points of H(13) (job cell-13-7).
# Builds the graph (multi.c, seed 1, S = Hermitian spread), checks it from all level-0 vertices and all hubs (apsp_src.c),
# exports the multi_sol.py solution and checks that it rebuilds the identical edge list.  Output in hex/ and multi_t/.
set -e
cd /home/user/degree-diameter/research/d13D7
R=$1; m=$(grep -c -v '^#' $R); N2=804468; n=$((5 * N2 + 4 * m))
tools/oppcheck hex/hex_q13.bin P $R | tail -1
RFILE=$R SFILE=q13/S_q13_spread.txt NOCHECK=1 ./multi hex/hex_q13.bin 2 1 hex/d16D7_R$m.edges
{ seq 0 $((N2 - 1)); seq $((5 * N2)) $((n - 1)); } > multi_t/src16_$m.txt
date -u +"%T apsp_src start"
OMP_NUM_THREADS=4 nice -n 2 ./apsp_src hex/d16D7_R$m.edges 16 7 multi_t/src16_$m.txt > hex/d16D7_R$m.apsp_src.txt 2> hex/d16D7_R$m.apsp_src.err
date -u +"%T apsp_src done"; cat hex/d16D7_R$m.apsp_src.txt
python3 tools/multi_sol.py export hex/d16D7_R$m.edges hex/hex_q13.bin 2 hex/d16D7_hex13_R${m}_n$n.sol
python3 tools/multi_sol.py build hex/d16D7_hex13_R${m}_n$n.sol hex/hex_q13.bin hex/_rt16.edges
cmp hex/d16D7_R$m.edges hex/_rt16.edges && echo "multi_sol round trip: byte-identical"
rm -f hex/_rt16.edges
