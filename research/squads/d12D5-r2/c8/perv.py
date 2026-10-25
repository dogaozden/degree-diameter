#!/usr/bin/env python3
# per-base-vertex singular walk counts from echart -p pattern files
import sys, subprocess, glob, os, collections
EA = [0,0,0,0,1,1,1,1,2,2,2,2]; EB = [0,0,1,2,1,1,0,2,2,2,0,1]   # base_k33m.txt edges
def analyse(ch):
    name = os.path.basename(ch).replace('.echart','')
    pat = os.path.join(os.path.dirname(os.path.abspath(__file__)), 'pat', name + '.pat')
    r = subprocess.run(['/home/user/degree-diameter/research/d12D5/echart', '/home/user/degree-diameter/research/d12D5/base_k33m.txt', '-p', ch, pat], capture_output=True, text=True, timeout=60)
    cnt = collections.Counter(); summ = r.stdout.strip()
    for line in open(pat):
        t = line.split()
        if t[0] == 'S':
            side = t[1]; e = [int(x) for x in t[2:6]]
            v = EA[e[1]] if side == 'A' else EB[e[1]]     # middle vertex of the walk
            cnt[(side, v)] += 1
    per = [sum(cnt[(s, v)] for s in 'AB' for _ in [0]) for v in range(3)]
    tot = {v: cnt[('A', v)] + cnt[('B', v)] for v in range(3)}
    return name, summ, [cnt[('A', v)] for v in range(3)], [cnt[('B', v)] for v in range(3)]
for ch in sys.argv[1:]:
    name, summ, a, b = analyse(ch)
    print(f"{name:16s} A={a} B={b} sum={sum(a)+sum(b)} | {summ}")
