#!/bin/bash
# usage: screen_shapes.sh OUTDIR  -- random-S screen of each orbit shape on candidate groups N in (12049800, 12100000]
OUT=$1; mkdir -p "$OUT"; cd "$(dirname "$0")/../.."
for kmf in "2 4 1" "2 3 3" "2 2 5" "4 2 1" "3 2 3" "5 1 4" "6 1 3" "8 1 1" "7 1 2" "3 3 0"; do echo "$kmf"; done | \
  xargs -P 4 -I{} bash -c 'kmf="{}"; tag=$(echo $kmf | tr " " _); OMP_NUM_THREADS=1 python3 tools/orb_screen.py 9 10 12049801 12100000 "$kmf" --samples 150 --top 60 > "'"$OUT"'/shape_$tag.txt" 2>&1'
echo SCREEN_DONE > "$OUT/DONE"
