#!/bin/bash
# tier 3: the μ ≈ 33.2 orders just above the record (N = 9,068,400 and 9,067,872), four jobs in parallel
cd "$(dirname "$0")"
../../tools/raise_run.sh 4000 1 prod_psl5_psl11_229_s1 prod psl 5 psl 11 229 &
../../tools/raise_run.sh 4000 2 prod_psl5_psl11_229_s2 prod psl 5 psl 11 229 &
ORBW=3 ../../tools/raise_run.sh 4000 3 prod_psl5_psl11_229_orbw3_s3 prod psl 5 psl 11 229 &
../../tools/raise_run.sh 4000 1 sl32_277_s1 sl 32 277 &
wait
