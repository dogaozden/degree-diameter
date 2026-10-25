#!/bin/bash
# tier 2: four jobs in parallel, ORBW=3 (uncovered fixed element weighs 3); restart variant on sl 29 x 373
cd "$(dirname "$0")"
ORBW=3 ../../tools/raise_run.sh 4000 2 sl29_373_orbw3_s2 sl 29 373 &
ORBW=3 ../../tools/raise_run.sh 4000 2 sl53_61_orbw3_s2 sl 53 61 &
ORBW=3 RESTART=1 ../../tools/raise_run.sh 4000 3 sl29_373_orbw3_restart_s3 sl 29 373 &
ORBW=3 ../../tools/raise_run.sh 4000 2 psl263_orbw3_s2 psl 263 1 &
wait
