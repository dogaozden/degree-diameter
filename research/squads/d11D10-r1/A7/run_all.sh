#!/bin/bash
# A7: Frobenius alpha (AFROB=1, order 5 on GF(32)) with z -> r z on Z_n, ORBIT="5 2 1".
# One gate slot: RANDORB=30 on sl 32 x Z2311 and sl 32 x Z2281, then a 360 s anneal (ORBW=5) on the group with the
# lower predicted mu_A (Z2281: mu 25.75, mu_A ~ 5.47; Z2311: mu 31.65, mu_A ~ 6.65).
H=/home/user/degree-diameter/research/structured/haar_sym
D=/home/user/degree-diameter/research/squads/d11D10-r1/A7
cd "$D" || exit 1
for n in 2311 2281; do
  env ORBIT="5 2 1" AFROB=1 RANDORB=30 "$H" 11 10 1 1 8 /dev/null sl 32 "$n" > "randorb_sl32_$n.log" 2>&1
  echo "randorb n=$n rc=$? $(date -u +%T)" >> screen.status
done
echo "anneal n=2281 start $(date -u +%T)" >> screen.status
exec env ORBIT="5 2 1" AFROB=1 ORBW=5 "$H" 11 10 360 1 8 "$D/d11D10_sl_32_2281_orb5_frob_s1.txt" sl 32 2281 > anneal_sl32_2281.log 2>&1
