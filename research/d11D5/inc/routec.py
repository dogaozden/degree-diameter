"""Apply route-(c) repairs to a switch base: for each switched point p_i (lost line L_i), set sigma(p_i) = L_i by
swapping with the current preimage of L_i.  Also the dual for lines (sigma^-1(L_i) = p_i is the same move).
usage: python3 routec.py in.in switch.json|auto out.in   (auto: find switched pairs from W(8) by comparing lines)"""
import sys, os
D = os.path.join(os.path.dirname(os.path.abspath(__file__)), ".."); sys.path.insert(0, D)
here = os.getcwd(); os.chdir(D)
from dcover import load
n0, L0, d_pt, d_ln, inv = load(8); os.chdir(here)
f = open(sys.argv[1]).read().split(); n, dg = int(f[0]), int(f[1])
ln = [list(map(int, f[2 + l * dg:2 + (l + 1) * dg])) for l in range(n)]; sig = list(map(int, f[2 + n * dg:2 + n * dg + n]))
pairs = []
for l in range(n0):
    for p in set(L0[l]) - set(ln[l]): pairs.append((p, l))
print("switched flags", pairs)
pos = {v: i for i, v in enumerate(sig)}
for p, l in pairs:
    a, b = p, pos[l]
    sig[a], sig[b] = sig[b], sig[a]; pos[sig[a]] = a; pos[sig[b]] = b
with open(sys.argv[3], "w") as g:
    g.write(f"{n} {dg}\n")
    for s in ln: g.write(" ".join(map(str, s)) + "\n")
    for v in sig: g.write(f"{v}\n")
