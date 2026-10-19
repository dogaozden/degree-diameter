#!/bin/bash
# One haar_search3 job per call: run_h3.sh d table secs
# Log: logs/h3_<tag>.log. Solution (only written on cost 0): sols/h3_<tag>.txt
# exec, so the PID the batch driver holds is the search process itself (kill reaches it).
cd /Users/dogaozden/AI_Projects/degree-diameter/research/d5 || exit 1
d=$1; table=$2; secs=$3
tag="d${d}_${table}"
exec ./haar_search3 "$d" "tables/$table.txt" 1 "$secs" "sols/h3_$tag.txt" 1 > "logs/h3_$tag.log" 2>&1
