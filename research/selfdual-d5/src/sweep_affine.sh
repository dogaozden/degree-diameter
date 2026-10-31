#!/bin/bash
# sweep_affine.sh LIST [P]: run_gapf.sh with src/affine_group.g on every "n p d k E o" line of LIST (affine_list.py).
cd "$(dirname "$0")/.."
awk '{printf "%s aff%s_%s_%s_%s src/affine_group.g P0:=%s;;D0:=%s;;K0:=%s;;E0:=%s;;\n", $1, $2, $3, $4, $6, $2, $3, $4, $5}' "$1" | xargs -P ${2:-1} -L 1 src/run_gapf.sh
echo "SWEEP DONE $1 $(date -u +%H:%M)" >> ${LOGDIR:-logs/K${K:-10}}/gapf.txt
