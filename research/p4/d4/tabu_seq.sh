#!/bin/bash
# usage: tabu_seq.sh secs inst:k0 ...
secs=$1; shift
for a in "$@"; do inst=${a%%:*}; k=${a##*:}; b=$(basename $inst .txt)
  for seed in 1 2; do runs/hs runs/$inst $k $secs $seed runs/hs_${b}_s$seed.out > runs/hs_${b}_s$seed.log 2>&1; done
done
