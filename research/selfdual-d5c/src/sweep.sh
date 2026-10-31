#!/bin/bash
# sweep.sh LIST W I: worker I of W over LIST (lines "N m k r d" for meta, or "N kind args..."), run1.sh on every
# line with index = I mod W that has no line yet in logs/K$K/runs.txt for the same tag; env passed through (K, SECS,
# TYPES, TAG, ...).  Stops when logs/K$K/STOP exists.
R0="$(cd "$(dirname "$0")/.." && pwd)"; L=$R0/logs/K${K:-12}
i=0
while read -r N a b c d e; do
    [ -e $L/STOP ] && break
    if [ $(( i % $2 )) -eq $3 ]; then
        case "$a" in psl|sl) args="$a $b $c";; meta|aff) args="$a $b $c $d $e";; *) args="meta $a $b $c 1";; esac
        tag=$(echo "$args" | tr ' ' '_')${TAG:+_$TAG}
        grep -q "^$tag " $L/runs.txt 2>/dev/null || $R0/src/run1.sh $args
    fi
    i=$((i + 1))
done < $1
