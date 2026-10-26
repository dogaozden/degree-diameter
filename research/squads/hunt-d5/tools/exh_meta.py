"""Exhaustive Haar search over a metacyclic group Z_m x|_r Z_k (big-squad-4-8 job), up to automorphisms.
Prints voltage lines "0 x y z" for flift eval (flift's meta index: a + m*j, left multiplication) with x running over
orbit representatives of the automorphisms (a, j) -> (u a + c [j], j), [j] = (r^j - 1)/(r - 1) (needs gcd(r-1, m) = 1),
and {y, z} over all unordered pairs of the remaining elements. Every Haar graph H(G, S) is isomorphic to one listed.
Usage: python3 exh_meta.py m k r [--reps] [--slice i/n] | flift BASE meta:m:k:r 4 D eval   (LIMIT=c ONLYLOW=1 for the low ones)"""
import sys
from math import gcd
m, k, r = map(int, sys.argv[1:4])
assert pow(r, k, m) == 1 % m and gcd(r - 1, m) == 1, "needs r^k = 1 and r - 1 a unit mod m"
inv = pow(r - 1, -1, m)
units = [u for u in range(1, m) if gcd(u, m) == 1]
reps = []
for j in range(k):
    br = (pow(r, j, m) - 1) * inv % m          # [j]
    seen = set()
    for a in range(m):
        if a in seen:
            continue
        orb = {(u * a + c * br) % m for u in units for c in range(m)}
        seen |= orb
        if not (j == 0 and a == 0):
            reps.append(a + m * j)
if "--reps" in sys.argv:
    print(len(reps), reps, file=sys.stderr)
    sys.exit()
N = m * k
out = sys.stdout
if "--slice" in sys.argv:                     # --slice i/n: only every n-th representative, starting at i
    i, n = map(int, sys.argv[sys.argv.index("--slice") + 1].split("/"))
    reps = reps[i::n]
for x in reps:
    others = [g for g in range(1, N) if g != x]
    for i, y in enumerate(others):
        out.write("".join(f"0 {x} {y} {z}\n" for z in others[i + 1:]))
