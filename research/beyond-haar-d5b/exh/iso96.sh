#!/bin/bash
# isomorphism classes of all order-96 solutions (both bases), by nauty canonical graph6
out=runs/iso96.txt; : > /tmp/claude-0/all96.lab
for f in runs/b4a1x_96_*.sol runs/b4a2y_96_*.sol; do
  [ -s $f ] || continue
  i=$(basename $f .sol | sed 's/.*_96_//'); p=$(basename $f .sol | cut -d_ -f1)
  [ -f /tmp/claude-0/t96_$i.txt ] || gap -q -c "ORDER:=96; ID:=$i; OUT:=\"/tmp/claude-0/t96_$i\";" gap_tab_gens.g > /dev/null 2>&1
  while read -r l; do python3 lift_edges.py /tmp/claude-0/t96_$i.txt "$l" /tmp/claude-0/x.edges 2>/dev/null
    python3 -c "
import sys
L=open('/tmp/claude-0/x.edges').read().split('\n'); n=int(L[0]); adj=[[0]*n for _ in range(n)]
for l in L[1:]:
    if l.strip(): a,b=map(int,l.split()); adj[a][b]=adj[b][a]=1
bits=[adj[i][j] for j in range(1,n) for i in range(j)]; bits+=[0]*(-len(bits)%6)
s='~'+''.join(chr(63+((n>>k)&63)) for k in (12,6,0))
print(s+''.join(chr(63+int(''.join(map(str,bits[i:i+6])),2)) for i in range(0,len(bits),6)))" | nauty-labelg -q 2>/dev/null | sed "s/\$/ $p 96_$i/" >> /tmp/claude-0/all96.lab
  done < <(grep SOL $f)
done
awk '{c[$1]++; g[$1]=g[$1]" "$2":"$3} END{for(k in c) print c[k], g[k]}' /tmp/claude-0/all96.lab | awk '{n=split($0,a," "); delete s; out=""; for(i=2;i<=n;i++) if(!(a[i] in s)){s[a[i]]=1; out=out" "a[i]}; print $1" solutions:"out}' | sort -rn > $out
echo "$(wc -l < $out) isomorphism classes among $(wc -l < /tmp/claude-0/all96.lab) solutions" >> $out
cat $out
