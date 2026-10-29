#!/bin/bash
# (7,5): h=2 coset graphs (orbit-type Haar allowed) of all groups of small-count orders 1204..1252, quick (500K + SA 40 s)
for on in "1228 4" "1244 4" "1252 5" "1204 13" "1208 12" "1212 12" "1236 15" "1220 20" "1240 51"; do set -- $on
  ./sweep_sa2.sh $1 2 7 40 "[1..$2]" > /dev/null 2>&1; echo "done $1" >> logs/batch10.out
done
echo BATCH10_DONE >> logs/batch10.out
