#!/bin/bash
# tier 4: replace the three prod jobs (cost in the thousands, abandoned) with two more seeds
cd "$(dirname "$0")"
../../tools/raise_run.sh 3600 2 sl32_277_s2 sl 32 277 &
ORBW=3 ../../tools/raise_run.sh 3600 4 sl53_61_orbw3_s4 sl 53 61 &
wait
