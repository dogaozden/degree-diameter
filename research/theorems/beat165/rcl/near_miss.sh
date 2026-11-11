#!/bin/bash
# usage: near_miss.sh TABLE k seed restarts steps tag : pvctrl3 best controller -> fitq exact chart fit (q=4)
S=/tmp/claude-0/-home-user-degree-diameter/f8a36126-b548-5f60-bd9a-01a3e8198698/scratchpad
out=$(./pvctrl3 $1 $2 $3 $4 $5 tables_g64_43.txt)
line=$(echo "$out" | grep "^BEST")
echo "$6 seed $3: $line" >> near_miss.log
python3 - "$1" "$line" "$S/nm_ctrl_$6_$3.txt" << 'EOP'
import sys
T = [list(map(int, l.split())) for l in open(sys.argv[1]) if l.strip()]
m = len(T); f = sys.argv[2].split()
k = int(f[2].split('=')[1]); nb = 2 * k
i = f.index('pa'); pa = list(map(int, f[i+1:i+1+nb])); i = f.index('pb'); pb = list(map(int, f[i+1:i+1+nb]))
i = f.index('fa'); fa = list(map(int, f[i+1:i+1+nb])); i = f.index('fb'); fb = list(map(int, f[i+1:i+1+nb]))
n = nb * m; sa = [0]*n; sb = [0]*n
for v in range(nb):
    for g in range(m):
        sa[v*m+g] = pa[v]*m + T[fa[v]][g]; sb[v*m+g] = pb[v]*m + T[fb[v]][g]
open(sys.argv[3], 'w').write(f'{n} {k*m}\n' + ' '.join(map(str, sa)) + '\n' + ' '.join(map(str, sb)) + '\n')
EOP
r=$(STRIDE=$(python3 -c "print(open(\"$S/nm_ctrl_$6_$3.txt\").read().split()[0])" | awk -v k=$2 '{print $1/(2*k)}') ./fitq 4 $S/nm_ctrl_$6_$3.txt $3 2000 60 chart_g64_43.txt | tail -2 | tr '\n' ' ')
echo "$6 seed $3 fit: $r" >> near_miss.log
