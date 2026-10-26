#!/bin/bash
# build group tables for every line in screen_list.txt
T=/home/user/degree-diameter/research/squads/b48/tools
cd /home/user/degree-diameter/research/squads/b48/r2/a09
i=0
while IFS=$'\t' read -r kind N spec; do
  i=$((i+1))
  if [ "$kind" = abc ]; then
    name="abc_${N}_$(echo $spec | tr ' ,:' '___')"
    THREADS=1 timeout 120 nice -n 10 python3 $T/abc.py build "$spec" grp/$name.bin >/dev/null 2>grp/$name.err || echo "FAIL $name"
  else
    name="meta_${N}_$(echo $spec | awk '{print $2"_"$3"_"$4}')"
    THREADS=1 timeout 120 nice -n 10 python3 $T/groups.py "$spec" grp/$name.bin >/dev/null 2>grp/$name.err || echo "FAIL $name"
  fi
  echo -e "$kind\t$N\t$spec\t$name" >> names.txt
done < screen_list.txt
