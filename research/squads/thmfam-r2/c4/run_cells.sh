#!/bin/bash
# usage: run_cells.sh T restarts budget "q m" ...   (c4 cells; uses cscan, base<q>.txt)
T=$1; R=$2; B=$3; shift 3
for qm in "$@"; do set -- $qm; nice -n 10 timeout 900 ./cscan $1 $2 $T $R $B 1 < base$1.txt; done
