#!/bin/bash
T=/home/user/degree-diameter/research/squads/b48/tools
D=/home/user/degree-diameter/research/squads/b48/r2/a08/tables
i=0
while read kind a b c d; do
  i=$((i+1))
  name=$(printf "g%02d_%s" $i "$kind")
  if [ "$kind" = abc ]; then
    timeout 120 nice -n 10 python3 $T/abc.py build "$a $b" $D/$name.bin | tail -1
  else
    timeout 120 nice -n 10 python3 $T/groups.py "meta $a $b $c" $D/$name.bin | tail -1
  fi
  echo "$name $kind $a $b $c $d"
done < /home/user/degree-diameter/research/squads/b48/r2/a08/specs.txt
