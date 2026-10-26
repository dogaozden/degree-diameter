#!/bin/bash
# sweep_specs.sh SPECFILE : for each group spec, build its table (groups.py) and run exhaustive haar_tab scan at D=11
D=${D:-11}
while read -r line; do
  [ -z "$line" ] && continue
  tag=$(echo "$line" | tr ' ' '_')
  timeout 900 nice -n 10 python3 /home/user/degree-diameter/research/squads/b48/tools/groups.py "$line" tabs/$tag.bin >/dev/null 2>&1 || { echo "SKIP $line"; continue; }
  out=$(timeout 900 nice -n 10 ./haar_tab tabs/$tag.bin $D scan)
  echo "$line | $out"
  rm -f tabs/$tag.bin
done < "$1"
