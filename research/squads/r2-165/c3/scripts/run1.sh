#!/bin/bash
# usage (one job): run1 TAG BASE TABLE PATTERN SECS SEED T0
# prints one line: TAG best_cost=... ; writes out/TAG.edges only when best_cost=0 (mlift_chart does that)
TAG="$1"; BASE="$2"; TABLE="$3"; PAT="$4"; SECS="$5"; SEED="$6"; T0="$7"
OUT=/tmp/claude-0/r2c3/out/$TAG.edges
R=$(cd /home/user/degree-diameter/research/theorems/squad165 && timeout 900 nice -n 10 /tmp/claude-0/r2c3/mlift_chart "$BASE" "$TABLE" "$PAT" "$SECS" "$SEED" "$T0" "$OUT" 2>&1 | head -1)
echo "$TAG $(basename "$BASE") $(basename "$TABLE") $(basename "$PAT") $(echo "$R" | sed -n 's/.*best_cost=\([0-9]*\).*/best_cost=\1/p')"
