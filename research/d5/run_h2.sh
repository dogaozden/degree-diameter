#!/bin/bash
# One haar_search2 job per call: run_h2.sh d N m k lam secs
# Log: logs/h2_<tag>.log. Solution (only written on cost 0): sols/h2_<tag>.txt
cd /Users/dogaozden/AI_Projects/degree-diameter/research/d5 || exit 1
d=$1; N=$2; m=$3; k=$4; lam=$5; secs=$6
tag="d${d}_N${N}_m${m}_k${k}_l${lam}"
./haar_search2 "$d" "$m" "$k" "$lam" 1 "$secs" "sols/h2_$tag.txt" 1 > "logs/h2_$tag.log" 2>&1
