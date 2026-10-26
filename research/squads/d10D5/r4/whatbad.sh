#!/bin/bash
# whatbad.sh STATE C0 "FDSET": exact failing base pairs of a FLAGDEL state (build_fd + BFS)
T=$(mktemp -d); ./finish_fd.sh "$1" "$2" "$3" $T/w > /dev/null 2>&1; tail -n 1 $T/w.log > /dev/null
python3 failpairs.py $T/w.fd.edges | awk '{split($1,a,"."); split($2,b,"."); if (a[1] < b[1]) print a[1] "-" b[1] "(" b[2] ")"}' | sort -u | tr '\n' ' '; echo
