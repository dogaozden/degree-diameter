#!/bin/bash
# scan.sh SRCSPEC SPEC... : random-voltage designs at q=5 (hex rand, phi rand), cost per group
SRC=$1; shift
for g in "$@"; do
  python3 mk_nl.py 5 $g 7 rand rand scan/s5_$g > /dev/null 2>&1 || { echo "$g: mk failed"; continue; }
  out=$(timeout 900 nice -n 10 ./nlift scan/s5_$g.grp scan/s5_$g.base 8 $SRC 2>/dev/null)
  echo "$g $out" | cut -c1-120
done
