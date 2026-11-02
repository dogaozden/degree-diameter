#!/bin/bash
# savegraph.sh EDGES NAME d D [extra files...]: gzip the edge list to ../beyond/graphs/NAME.edges.gz, run apsp (all pairs)
# through check_one.sh into ../beyond/checks/NAME.apsp.txt, copy extra files (voltages, solution) to ../beyond/graphs/.
cd "$(dirname "$0")"; e=$1; name=$2; d=$3; D=$4; shift 4
mkdir -p ../beyond/graphs ../beyond/checks
gzip -c "$e" > ../beyond/graphs/$name.edges.gz
OMP_NUM_THREADS=${CTH:-1} ./check_one.sh apsp ../beyond/checks/$name.apsp.txt ./bin/apsp "$e" $d $D
for x in "$@"; do cp "$x" ../beyond/graphs/$name.$(basename "$x" | sed 's/.*\.//'); done
grep -h "RESULT" ../beyond/checks/$name.apsp.txt
