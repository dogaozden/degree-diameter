#!/bin/bash
# B8 metacyclic screen: G = Z_p x|_r Z_c (r of order 5, p prime = 1 mod 5), ORBIT "5 2 1" (automatic meta scaling alpha),
# RANDORB=30 each, then the k = 3 baseline psl 149 x Z43 with RANDORB=100 for calibration. One gate slot, sequential.
H=/home/user/degree-diameter/research/structured/haar_sym
D=/home/user/degree-diameter/research/squads/d11D10-r1/B8
unset THREADS
cd "$D" || exit 1
for spec in "14223691 5 3428689" "7111771 10 2862052" "3555901 20 2543008" "1777981 40 478275"; do
  set -- $spec
  echo "=== meta p=$1 c=$2 r=$3 (N=$(( $1 * $2 )))"
  env ORBIT="5 2 1" RANDORB=30 "$H" 11 10 1 1 8 /dev/null meta $1 $2 $3 1
  echo "rc=$?"
done
echo "=== baseline psl 149 x Z43 k=3"
env ORBIT="3 3 2" RANDORB=100 "$H" 11 10 1 1 8 /dev/null psl 149 43
echo "rc=$?"
