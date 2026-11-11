#!/bin/bash
# check.sh SOL.txt : full independent check of a Haar solution file (haar_sym2 / haar_gen3 format) at its own d, D.
# Runs research/frontier/haarcheck_gen (C, low memory) and research/frontier/build_haar2.py (numpy), writes both
# outputs to SOL.check.txt next to the file, prints the verdict. Heavy (minutes, ~2 GB for build_haar2 at 1.2M
# vertices): run it ONLY on a file that your search says has cost 0.
set -u
R=/home/user/degree-diameter/research
S=$1; C=${S%.txt}.check.txt
[ -x $R/frontier/haarcheck_gen ] || gcc -O3 -fopenmp -o $R/frontier/haarcheck_gen $R/frontier/haarcheck_gen.c
{ echo "# checks of $S ($(date -u +%FT%TZ))"; echo "## haarcheck_gen"; OMP_NUM_THREADS=1 timeout 3000 nice -n 5 $R/frontier/haarcheck_gen $S 2>&1 | tail -4
  echo "## build_haar2.py"; timeout 5000 nice -n 5 python3 $R/frontier/build_haar2.py $S 2>&1 | tail -8; echo "## sha256 $(sha256sum $S)"; } > $C
cat $C
