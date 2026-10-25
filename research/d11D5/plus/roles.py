import json, sys, os
from collections import Counter
sys.path.insert(0, "/home/user/degree-diameter/research/d11D5"); here=os.getcwd(); os.chdir("/home/user/degree-diameter/research/d11D5")
from dcover import load
n, L, d_pt, d_ln, inv = load(8); os.chdir(here)
d = json.load(open(sys.argv[1])); lines, pts = d["lines"], d["pts"]
N = 586
role = {}
def addr(v, r): role.setdefault(v, set()).add(r)
for i,(li,p) in enumerate(zip(lines,pts)):
    addr(p, "p_i"); addr(N+li, "L_i"); addr(d_ln[li], "d(L_i)"); addr(N+d_pt[p], "d(p_i)")
    for q in L[li]:
        if q!=p: addr(q, "z")
    for m in range(n):
        if p in L[m] and m!=li: addr(N+m, "m"); addr(d_ln[m], "d(m)")
addr(585,"x*"); addr(2*N-1,"l*")
def r(v): return "+".join(sorted(role.get(v, {"P" if v < N else "L"})))
rows = [tuple(map(int, l.split()[-4:])) for l in open(sys.argv[2])]
c = Counter((r(s), r(t), cc) for s,t,cc,dd in rows)
for k,v in c.most_common(int(sys.argv[3]) if len(sys.argv)>3 else 20): print(v, k)
