#!/bin/bash
# verify.sh SOL.txt: independent checks of a (10,8) Haar solution found by haar_sym, and filing.
# Runs research/frontier/build_haar2.py and research/frontier/check_haar_indep.py, writes both outputs next to the
# solution as SOL.check.txt, and copies the solution to research/frontier/sols/ (name unchanged, starts with d10D8_).
set -u
R=/home/user/degree-diameter/research
S=$1; B=$(basename $S .txt); C=$(dirname $S)/$B.check.txt
{ echo "# independent checks of $B ($(date -u +%Y-%m-%dT%H:%M:%SZ))"; echo "## build_haar2.py"; timeout 3000 python3 $R/frontier/build_haar2.py $S 2>&1 | tail -6
  echo "## check_haar_indep.py"; timeout 3000 python3 $R/frontier/check_haar_indep.py $S 2>&1 | tail -4; } > $C
cat $C
if grep -q "^VALID" $C && grep -q "RESULT VALID" $C; then cp $S $R/frontier/sols/$B.txt; echo "BOTH VALID: copied to frontier/sols/$B.txt"; else echo "NOT BOTH VALID"; fi
