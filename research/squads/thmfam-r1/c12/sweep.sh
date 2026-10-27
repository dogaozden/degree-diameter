#!/bin/bash
# usage: sweep.sh kind norb seed ; prints q Delta diam connected
H=/home/user/degree-diameter/research/theorems/haar_families/haar_ecc
D=/home/user/degree-diameter/research/squads/thmfam-r1/c12
kind=$1; norb=$2; seed=$3
for q in 5 7 11 13 17 19 23 29 31 37 41 43 47 53 59 61; do
  out=$(python3 $D/gen_torus.py $q $kind $norb $seed 2>$D/.err | nice -n 10 timeout 900 $H psl $q 1)
  dl=$(sed -n 's/.*Delta=\([0-9]*\) q=.*/\1/p' $D/.err)
  echo "$out" | sed -n 's/.*q=\([0-9]*\) .*Delta=\([0-9]*\).*connected=\([a-z]*\) diam=\([0-9]*\).*/q=\1 Delta=\2 connected=\3 diam=\4/p' | tr '\n' ' '; echo
done
