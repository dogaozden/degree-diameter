#!/usr/bin/env python3
# singular-walk sets from echart -p pattern files; prints per-chart digest and overlap with a reference chart
import sys, subprocess, os, hashlib
EA = [0,0,0,0,1,1,1,1,2,2,2,2]; EB = [0,0,1,2,1,1,0,2,2,2,0,1]
def sing(ch):
    name = os.path.basename(ch).replace('.echart','')
    pat = os.path.join('/home/user/degree-diameter/research/squads/d12D5-r2/c8/pat', name + '.pat')
    subprocess.run(['/home/user/degree-diameter/research/d12D5/echart', '/home/user/degree-diameter/research/d12D5/base_k33m.txt', '-p', ch, pat], capture_output=True, text=True, timeout=60)
    S = set(); P = []
    for line in open(pat):
        t = line.split()
        if t[0] == 'S': S.add((t[1],) + tuple(int(x) for x in t[2:6]))
        elif t[0] == 'P': P.append(tuple(t))
    return S, P
ref = None
for ch in sys.argv[1:]:
    S, P = sing(ch)
    d = hashlib.md5(repr(sorted(S)).encode()).hexdigest()[:8]
    print(f"{os.path.basename(ch):18s} nS={len(S)} pencil={len(P)} setdig={d}", end='')
    if ref is None: ref = S
    print(f" overlap_with_first={len(S & ref)}")
