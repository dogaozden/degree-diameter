#!/bin/bash
cd /home/user/degree-diameter/research/squads/table-audit-r1/c6
for cfg in "8 100" "16 50" "32 25" "4 200"; do
  set -- $cfg
  ./sym_anneal $1 $2 10 100 7 g_n800_b$1_c$2_D10.txt 3.0 0.1 2000000 2>/dev/null
done
