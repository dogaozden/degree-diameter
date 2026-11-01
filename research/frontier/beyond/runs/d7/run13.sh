#!/bin/bash
cd "$(dirname "$0")"
for x in "13 3" "13 4"; do set -- $x
  echo "== q=$1 r=$2 start $(date -u +%T)"; nice -n 2 ./dirlift7 $1 $2 1 bfs 64; echo "== end $(date -u +%T)"
done
