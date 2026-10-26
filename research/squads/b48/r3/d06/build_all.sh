#!/bin/bash
# builds the abc tables for the card d06 candidates (N in 2486..2900, non-metacyclic)
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r3/d06
while read k comps; do
  name=$(echo "$k|$comps" | tr ' ,:|@' '______')
  timeout 120 nice -n 10 python3 $T/abc.py build "$k $comps" bins/$name.bin >/dev/null 2>&1 || echo "FAIL $k $comps"
done <<'LIST'
3 29:3:2
3 7:3:1,11:3:2
9 17:9:2
11 3:11:5
3 5:3:2,37:3:1
3 7:3:1,7:3:1,19:3:1
3 7:3:1,7:3:1@2,19:3:1
3 31:3:1,31:3:1
3 31:3:1,31:3:1@2
LIST
ls bins
