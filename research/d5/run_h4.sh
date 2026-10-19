#!/bin/bash
# One haar_search3 job per call: run_h4.sh d table seed secs K
# Log: logs/h4_<tag>.log. Solution (only written on cost 0): sols/h4_<tag>.txt
# Builds the table with groups.py (checked) if it is not there yet. exec, so the PID the driver holds is the search.
cd /Users/dogaozden/AI_Projects/degree-diameter/research/d5 || exit 1
d=$1; table=$2; seed=$3; secs=$4; K=$5
tag="d${d}_${table}_s${seed}_K${K}"
[ -f "tables/$table.txt" ] || python3 groups.py --check "$table" >/dev/null || exit 1
exec ./haar_search3 "$d" "tables/$table.txt" "$seed" "$secs" "sols/h4_$tag.txt" "$K" > "logs/h4_$tag.log" 2>&1
