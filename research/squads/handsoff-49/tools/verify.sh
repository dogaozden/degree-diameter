#!/bin/bash
# verify.sh EDGES : independent all-pairs check (apsp.c) at d=4 D=9 and D=8. A record needs VALID at 9, INVALID at 8, n > 4970.
T=$(dirname "$0")
echo "D=9: $($T/apsp "$1" 4 9 | tr '\n' ' ')"
echo "D=8: $($T/apsp "$1" 4 8 | tail -1)"
