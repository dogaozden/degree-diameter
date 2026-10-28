#!/bin/bash
# generator lines of the LPS family for p=$1 at q=$2 (z = 0)
"$(dirname "$0")/lps_haar" $1 $2 -v | grep '^gen' | sed 's/.*mat(//; s/) z=/ /; s/,/ /g'
