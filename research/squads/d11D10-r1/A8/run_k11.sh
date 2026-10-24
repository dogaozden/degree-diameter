#!/bin/bash
# A8 wildcard: k = 11 single-orbit family, ORBIT="11 1 0" (S = one alpha-orbit, alpha = conj by order-11 g times z -> r z).
# G = PSL(2,23) x Z_12409 (12409 prime, 12408 = 11 * 1128): |G| = 75,347,448, vertices 150,694,896, mu = 29.7.
# Step 1: RANDORB screen (cost statistics, P(cost 0) of random symmetric S). Step 2: annealing, ORBW=11 (energy = uncovered alpha-clumps).
H=/home/user/degree-diameter/research/structured/haar_sym
A8=/home/user/degree-diameter/research/squads/d11D10-r1/A8
cd "$A8"
env ORBIT="11 1 0" RANDORB=400 "$H" 11 10 1 1 8 /dev/null psl 23 12409 > "$A8/randorb_k11_psl23_n12409.log" 2>&1
env ORBIT="11 1 0" ORBW=11 "$H" 11 10 480 1 8 "$A8/d11D10_psl_23_12409_orb11_A8_s1.txt" psl 23 12409 > "$A8/anneal_k11_psl23_n12409.log" 2>&1
echo "chain done rc=$?" >> "$A8/anneal_k11_psl23_n12409.log"
