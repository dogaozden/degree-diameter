"""Polarity-symmetric one-pair extension of W(8): pick k=9 absolute points p_i (on the Suzuki-Tits ovoid), replace the
absolute flags (p_i, delta(p_i)) by (x*, delta(p_i)) and (p_i, l*), delta(x*) = l*.  The result keeps a polarity.
usage: python3 mkpol.py seed out.in   (writes the plusopt2 input; sigma = extended polarity)"""
import sys, random
import os; sys.path.insert(0, "/home/user/degree-diameter/research/d11D5")
here = os.getcwd(); os.chdir(".."); from dcover import load; n, L, d_pt, d_ln, inv = load(8); os.chdir(here)
seed, out = int(sys.argv[1]), sys.argv[2]
rng = random.Random(seed)
L = [list(s) for s in L]
absol = [p for p in range(n) if p in L[d_pt[p]]]
pts = rng.sample(absol, 9) if seed >= 0 else absol[:9]
X = n
for p in pts:
    L[d_pt[p]].remove(p); L[d_pt[p]].append(X)
L.append(pts[:])
sigma = d_pt[:] + [n]
with open(out, "w") as f:
    f.write(f"{n+1} 9\n")
    for s in L: f.write(" ".join(map(str, s)) + "\n")
    f.write("\n".join(map(str, sigma)) + "\n")
print("absolute points", len(absol), "chosen", pts)
