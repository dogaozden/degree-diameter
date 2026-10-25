#!/bin/bash
# c7 (wildcard A): baseline annealer mirror_sa4.py (seed 1, default pool and T, --secs $SECS) from the identity base
# R756 (control, tag id) and from isometric copies of R756 (bases made by iso_base.py); each best state is re-scored by
# mirror_build.py.  One process at a time, single thread.  usage: run_c7.sh TAG [TAG ...]
export OMP_NUM_THREADS=1 OPENBLAS_NUM_THREADS=1 MKL_NUM_THREADS=1 NUMEXPR_NUM_THREADS=1
HERE=/home/user/degree-diameter/research/squads/d14D7-r6/c7
SC=/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/r6_c7
SECS=${SECS:-240}
cd "$HERE" || exit 1
for tag in "$@"; do
  if [ "$tag" = id ]; then RF=""; else RF="--rfile $SC/bases/R_$tag.npy"; fi
  timeout 900 nice -n 15 python3 mirror_sa4.py 1 "$SC/sa_$tag" --secs "$SECS" $RF > "$SC/sa_$tag.log" 2>&1
  timeout 900 nice -n 15 python3 mirror_build.py "$SC/sa_$tag/best.npz" 1 "$SC/build_$tag" > "$SC/build_$tag.log" 2>&1
  echo "$tag SA: $(grep 'best F' "$SC/sa_$tag.log" | tail -1) | build: $(grep -o "|R'| = [0-9]*" "$SC/build_$tag.log")" >> "$SC/summary.txt"
done
echo DONE >> "$SC/summary.txt"
