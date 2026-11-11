#!/bin/bash
# one job line "seed|GROUP... n"; env SECS (seconds) and K (candidates per move)
cd "$(dirname "$0")"
seed=${1%%|*}; grp=${1#*|}
./run1.sh "$SECS" "$seed" "$K" "$grp"
