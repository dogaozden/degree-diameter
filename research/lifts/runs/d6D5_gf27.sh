#!/bin/bash
# (6,5) at 702: Haar graphs of GF(27) x| Z13 (aff3, Singer-type M of order 13), 4 seeds x 300 s per matrix
cd "$(dirname "$0")/.."
python3 bases.py dipole 6 > bases/dipole6.txt
for M in $(python3 -c "
import sys; sys.path.insert(0,'.'); import groups
print(' '.join(s.split(' ',2)[2].rsplit(' ',1)[0].replace(' ','_') for s in groups.affs3(3,13)))"); do
  for s in 1 2 3 4; do
    ./lift search bases/dipole6.txt 5 300 $s 8 sols/d6D5_haar_aff3_${M}_13_s$s.txt aff3 3 ${M//_/ } 13 2>/dev/null | grep -E "RESULT|wrote"
  done
done
