import sys, math, re
# usage: es.py "<info output lines>"  -> prints census and E_s = sum over non-regular orbits of exp(-lambda*s/10)
lam = 5380840 / 592956
txt = open(sys.argv[1]).read()
m = re.search(r"by #R-cosets:(.*)", txt)
cen = {}
for tok in m.group(1).split():
    s, c = tok[1:].split(':'); cen[int(s)] = int(c)
E = sum(c * math.exp(-lam * s / 10) for s, c in cen.items() if s < 10)
print("census", " ".join(f"c{s}:{cen[s]}" for s in sorted(cen)), f"E_s={E:.3f}")
