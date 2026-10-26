#!/bin/bash
# hits.sh: list cost-0 haar_fast/haar_tab solution files and the farm summary (hunt-d5)
cd $(dirname $0)/..
echo "cost-0 solution files:"; find . -name "*.sol" -newer tools/haar5.c 2>/dev/null | while read f; do grep -q "best=0" $(dirname $f)/farm.log 2>/dev/null && echo "  $f"; done
grep -rhs "best=0 " --include=farm.log --include=*.log . | grep -v "min=0" | head -5
for d in tables/farm7c tables/farm7g tables/farm7h tables/farm7i tables/farm7j tables/farm9c; do echo "$d: $(grep -c seed= $d/farm.log) seeds; $(grep -o 'best=[0-9]*' $d/farm.log | sort -t= -k2 -n | uniq -c | head -4 | tr '\n' ' ')"; done
echo "cert queue: $(cat tables/certq6_*.log | tr '\n' ' ' | cut -c1-400)"
echo "exhp 216-240: $(cat tables/exhp_216_240_q*.log | grep -c RESULT) of 429 done; min=0 lines: $(cat tables/exhp_216_240_q*.log | grep -c 'min=0 ')"
