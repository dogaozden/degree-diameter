#!/bin/sh
# usage: shared/check.sh EDGES   (edge list: first number n, then "u v" pairs, 0-based)
# Prints the score65 line (bad = unordered pairs at distance > 5) and, if bad = 0, the apsp verdict at d=6 D=5.
H=$(dirname "$0")
"$H/score65" "$1"
if "$H/score65" "$1" | grep -q ' bad=0 '; then "$H/apsp_ref" "$1" 6 5; fi
