#!/bin/bash
# mon.sh: summary of the CHAIN lines of g4.log (ORBW=3 units; energy is a multiple of 3)
cd "$(dirname "$0")"
grep '^CHAIN' g4.log | awk '{print $4}' > mins.txt
n=$(wc -l < mins.txt)
[ "$n" -eq 0 ] && { echo "chains 0 at $(date -u +%T)"; exit 0; }
best=$(sort -n mins.txt | head -1)
med=$(sort -n mins.txt | awk '{a[NR]=$1} END{print a[int((NR+1)/2)]}')
c12=$(awk '$1<=12' mins.txt | wc -l); c9=$(awk '$1<=9' mins.txt | wc -l); c6=$(awk '$1<=6' mins.txt | wc -l); c3=$(awk '$1<=3' mins.txt | wc -l)
hist=$(sort -n mins.txt | uniq -c | awk '{printf "%s:%s ", $2, $1}')
echo "chains $n best $best median $med <=12: $c12 <=9: $c9 <=6: $c6 <=3: $c3 | hist $hist| at $(date -u +%T)"
