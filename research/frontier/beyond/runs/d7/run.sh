#!/bin/bash
# sampled BFS checks of the D=7 level graphs (squad r1/c09's lift7.c): 64 random sources each
cd "$(dirname "$0")"
for x in "16 2" "16 3" "13 3" "13 4"; do set -- $x
  echo "== q=$1 r=$2 start $(date -u +%T)"; nice -n 2 ./lift7 $1 $2 1 bfs 64; echo "== end $(date -u +%T)"
done
