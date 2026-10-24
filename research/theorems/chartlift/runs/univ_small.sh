#!/bin/bash
# universal 4-letter charts (no singular nonbacktracking 4-pattern) for every prime power 3 <= q <= 127
cd "$(dirname "$0")/.."
for q in 3 4 5 7 8 9 11 13 16 17 19 23 25 27 29 31 32 37 41 43 47 49 53 59 61 64 67 71 73 79 81 83 89 97 101 103 107 109 113 121 125 127; do
  [ -f charts/universal/k4_q$q.txt ] && python3 -c "
from chartlib import read_chart_txt
import sys
ch=read_chart_txt('charts/universal/k4_q$q.txt',$q,4); sys.exit(0 if not ch.singular_patterns() else 1)" && { echo "q=$q already"; continue; }
  timeout 900 nice -n 5 ./chart_anneal tables/gf$q.txt 4 600 $q 1 0 0 charts/universal/k4_q$q.txt | tail -1 | sed "s/^/q=$q /"
done
