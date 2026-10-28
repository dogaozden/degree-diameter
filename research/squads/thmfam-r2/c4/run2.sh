#!/bin/bash
# usage: run2.sh T restarts budget "q m" ...   (cscan2: z1 searched too; base<q>.txt)
T=$1; R=$2; B=$3; shift 3
for qm in "$@"; do set -- $qm; nice -n 10 timeout 900 ./cscan2 $1 $2 $T $R $B 7 < base$1.txt; done
