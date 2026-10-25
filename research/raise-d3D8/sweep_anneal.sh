#!/usr/bin/env bash
# usage: sweep_anneal.sh BASEFILE D TAG SECS SEED N... : anneal every group spec of each order N, 4 jobs in parallel
cd "$(dirname "$0")"
BASE=$1; D=$2; TAG=$3; SECS=$4; SEED=$5; shift 5
for N in "$@"; do python3 gen_specs.py "$N" --prod; done | xargs -P 4 -d '\n' -I@ ./run_anneal.sh "$BASE" "$D" "$TAG" "$SECS" "$SEED" @
