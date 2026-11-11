#!/bin/bash
# usage: hist.sh LOG...  -> per log: chains, min, median, count<=12, count<=9, count<=6 (field 4 of CHAIN lines)
for f in "$@"; do
  grep '^CHAIN' "$f" 2>/dev/null | awk '{print $4}' | sort -n | awk -v f="$f" '
    {v[NR]=$1} END{
      n=NR; if(n==0){printf "%s chains=0\n", f; exit}
      med=v[int((n+1)/2)]; c12=0;c9=0;c6=0
      for(i=1;i<=n;i++){if(v[i]<=12)c12++; if(v[i]<=9)c9++; if(v[i]<=6)c6++}
      printf "%s chains=%d min=%d median=%d <=12:%d <=9:%d <=6:%d\n", f, n, v[1], med, c12, c9, c6}'
done
