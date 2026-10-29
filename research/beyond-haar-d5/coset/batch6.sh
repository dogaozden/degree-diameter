#!/bin/bash
# h=2 coset graphs, Haar-type subgroups skipped, all SmallGroups of these orders (N = |G|)
for on in "1156 16" "1164 18" "1172 5" "1180 11" "1192 14" "1196 11" "1160 49" "1168 53" "1188 99"; do set -- $on
  ./sweep_nh.sh $1 2 7 20 "[1..$2]" > /dev/null 2>&1
  echo "done $1" >> logs/batch6.out
done
echo BATCH6_DONE >> logs/batch6.out
