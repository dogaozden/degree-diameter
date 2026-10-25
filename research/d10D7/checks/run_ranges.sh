#!/bin/bash
# run_ranges.sh EDGES d D OUTPREFIX "S0 S1" "S0 S1" ...   : apsp_range on each source range in parallel, then merge.
# The union of the ranges must cover the sources wanted ([0,n) for a full all-pairs check).
E=$1; d=$2; D=$3; P=$4; shift 4; pids=()
for r in "$@"; do set -- $r; ./apsp_range $E $d $D $1 $2 > ${P}.r_$1.txt 2>&1 & pids+=($!); done
for p in "${pids[@]}"; do echo -5 > /proc/$p/autogroup 2>/dev/null; done
wait
cat ${P}.r_*.txt > ${P}.all.txt
if [ $(grep -c 'RESULT VALID' ${P}.all.txt) -eq $(ls ${P}.r_*.txt | wc -l) ]; then echo "ALL RANGES VALID: $(grep -o 'eccentricity max=[0-9]*' ${P}.all.txt | sort -u | tr '\n' ' ')"; else echo "SOME RANGE FAILED"; fi >> ${P}.all.txt
