#!/bin/bash
# builds the remaining abc candidates (N in 2486..2900) and counts involutions
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r3/d06
while read k comps; do
  name=$(echo "$k|$comps" | tr ' ,:|@' '______')
  timeout 120 nice -n 10 python3 $T/abc.py build "$k $comps" bins/$name.bin >/dev/null 2>&1 || echo "FAIL $k $comps"
done <<'LIST'
12 2:3:2,2:3:2,13:12:1
12 2:3:2,2:3:2,13:4:1
3 2:3:2,211:3:1
12 2:3:2,53:4:1
4 13:4:1,7:4:2
8 13:4:1,5:8:2
3 2:3:2,7:3:1,31:3:1
6 2:3:2,109:6:1
4 3:4:2,73:4:1
9 2:3:2,73:9:1
15 11:5:1,2:15:4
15 2:3:2,2:3:2,11:5:1
8 3:8:2,37:4:1
18 2:3:2,37:18:1
3 2:3:2,223:3:1
21 2:3:2,2:3:2,2:7:3
12 3:4:2,5:12:2
12 3:4:2,5:3:2
12 3:4:2,5:6:2
9 2:3:2,2:3:2,19:9:1
3 2:3:2,229:3:1
24 3:8:2,13:12:1
24 3:8:2,13:3:1
24 3:8:2,13:6:1
6 19:3:1,5:6:2
6 19:6:1,5:3:2
6 19:6:1,5:6:2
20 3:4:2,2:5:4
8 19:8:2
3 2:3:2,241:3:1
4 5:4:1,5:4:1,29:4:1
4 5:4:1,5:4:1@3,29:4:1
LIST
