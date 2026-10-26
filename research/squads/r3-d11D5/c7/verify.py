"""Check a .in base is H-invariant and sigma is H-equivariant for the group file. usage: verify.py base.in group.grp"""
import sys
f = open(sys.argv[1]).read().split(); n, dg = int(f[0]), int(f[1])
ln = [[int(x) for x in f[2 + l * dg: 2 + (l + 1) * dg]] for l in range(n)]
sig = [int(x) for x in f[2 + n * dg: 2 + n * dg + n]]
g = open(sys.argv[2]).read().split(); G = int(g[0]); pos = 1
ok = sorted(sig) == list(range(n)) and all(len(set(s)) == dg for s in ln)
from collections import Counter
deg = Counter(p for s in ln for p in s); ok = ok and set(deg.values()) == {dg} and len(deg) == n
for k in range(G):
    gp = [int(x) for x in g[pos:pos + n]]; pos += n
    gl = [int(x) for x in g[pos:pos + n]]; pos += n
    for l in range(n):
        if sorted(gp[p] for p in ln[l]) != sorted(ln[gl[l]]): ok = False
    if any(gl[sig[p]] != sig[gp[p]] for p in range(n)): ok = False
print(sys.argv[1], "H-invariant, equivariant, dg-regular:", ok)
