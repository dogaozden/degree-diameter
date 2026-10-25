#!/bin/bash
# many CSP solutions (one per seed) with NV variants each, for K33m
for s in $(seq $1 $2); do timeout 100 python3 csp3.py ../base_k33m.txt 1 $s var2/p$s $3 > /dev/null 2>&1; done
