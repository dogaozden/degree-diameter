#!/bin/bash
# usage: exp.sh NAME "GAP expression for G"
cd /home/user/degree-diameter/research/squads/bh5b-r1/c3
timeout 600 nice -n 10 gap -q -o 1500m -c "Read(\"dc2_lib.g\"); G := $2; G := Image(IsomorphismPermGroup(G)); Print(\"ORDER \", Size(G), \"\\n\"); H_ORDER := 4; ExportPairs(G, H_ORDER, \"dc/$1\"); QUIT;" 2>&1 | tail -3
ls dc/$1_* 2>/dev/null | tr '\n' ' '; echo
