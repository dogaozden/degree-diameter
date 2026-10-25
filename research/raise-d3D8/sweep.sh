#!/usr/bin/env bash
# usage: sweep.sh BASEFILE D TAG N... : every group spec of each order N (metacyclic, Z_p^2 x| Z_k, products with cyclic), 4 jobs
cd "$(dirname "$0")"
BASE=$1; D=$2; TAG=$3; shift 3
for N in "$@"; do python3 gen_specs.py "$N" --prod; done | xargs -P 4 -I{} bash -c 'echo "{}" | xargs -d "\n" -I@ ./run_one.sh '"$BASE $D $TAG"' @' 
