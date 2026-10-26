#!/bin/bash
# hits.sh: list cost-0 haar_fast/haar_tab solution files and the farm summary (hunt-d5)
cd $(dirname $0)/..
echo "cost-0 solution files:"; find . -name "*.sol" -newer tools/haar5.c 2>/dev/null | while read f; do grep -q "best=0" $(dirname $f)/farm.log 2>/dev/null && echo "  $f"; done
grep -rhs "best=0 " --include=farm.log --include=*.log . | grep -v "min=0" | head -5
for d in tables/farm7c tables/farm7e tables/farm9b; do echo "$d: $(grep -c seed= $d/farm.log) seeds; $(grep -o 'best=[0-9]*' $d/farm.log | sort -t= -k2 -n | uniq -c | head -4 | tr '\n' ' ')"; done
echo "certificates done: 360/51 $(cat tables/cert360_r*.log | grep -c RESULT)/13, 351/5 $(cat tables/cert351_5_r*.log | grep -c RESULT)/9; any zero: $(cat tables/cert360_r*.log tables/cert351_5_r*.log | grep -c '^cost 0')"
