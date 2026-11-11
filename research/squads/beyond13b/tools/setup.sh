#!/bin/bash
# setup.sh: build the search and check tools into research/frontier/beyond13/bin (about 30 s). Run from the repo root.
set -e
cd "$(git rev-parse --show-toplevel)/research/frontier/beyond13"; mkdir -p bin
F="-O3 -march=native -fopenmp"
gcc $F -o bin/haar_big0 ../beyond11/haar_big0.c -lm 2>/dev/null
gcc $F -o bin/hmeta meta/hmeta.c -lm 2>/dev/null
gcc $F -o bin/haar_gen3 ../haar_gen3.c -lm 2>/dev/null
gcc $F -o bin/haarcheck_gen ../haarcheck_gen.c -lm 2>/dev/null
gcc $F -o bin/haar_gen3s ../../squads/beyond11b/tools/haar_gen3s.c -lm 2>/dev/null
gcc $F -o bin/haar_gen3t ../../squads/beyond11b/tools/haar_gen3t.c -lm 2>/dev/null
gcc -O3 -march=native -fopenmp -o bin/apsp ../../lifts/coordinator_check/apsp.c -lm 2>/dev/null
ls bin
