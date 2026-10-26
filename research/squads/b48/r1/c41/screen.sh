#!/bin/bash
# c41 screen: screen.sh BASE_FILE_STEM N SECONDS [specs...]; each group: phigen (table + phi), then parlift D=8
cd /home/user/degree-diameter/research/squads/b48/r1/c41
base=$1; N=$2; secs=$3; shift 3
specs=("$@")
for spec in "${specs[@]}"; do
  tag=$(echo "$spec" | tr ' ' '_')_$base
  THREADS=1 timeout 120 nice -n 10 python3 phigen.py "$spec" grp/$tag >/dev/null 2>grp/$tag.err || { echo "PHIFAIL $spec"; continue; }
  res=$(THREADS=1 timeout 120 nice -n 10 ./parlift bases/$base.txt grp/$tag.bin grp/$tag.phi 8 $secs 1 8 2>&1 | grep RESULT)
  echo "$base | $spec | $res"
done
