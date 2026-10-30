#!/bin/bash
# (7,5) orbit-type Haar graphs of odd-order groups: h=2 coset graphs of the groups of order 2 x odd, SA 120 s
for on in "1210 27" "1206 16" "1218 16" "1230 12" "1170 32" "1190 8" "1194 6" "1242 30" "1158 6" "1162 4" "1166 4" "1178 4" "1182 4" "1222 4" "1246 4" "1174 2" "1186 2" "1198 2" "1202 2" "1214 2" "1226 2" "1234 2" "1238 2"; do set -- $on
  ./sweep_sa.sh $1 2 7 120 "[1..$2]" > /dev/null 2>&1; echo "done $1" >> logs/batch9.out
done
echo BATCH9_DONE >> logs/batch9.out
