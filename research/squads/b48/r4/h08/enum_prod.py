# Non-abelian direct products A x B of cyclic / dihedral groups of order N in [127,140] (not already metacyclic-listed),
# deduped by element-order multiset and centre size. Writes spec lines and .bin tables into bins/.
import sys, os, collections
import numpy as np
sys.path.insert(0, "/home/user/degree-diameter/research/squads/b48/tools")
import groups
os.makedirs("bins", exist_ok=True)
def inv(T):
    N = len(T)
    ords = []
    for x in range(N):
        o, y = 1, x
        while y != 0:
            y = T[y, x]; o += 1
        ords.append(o)
    cen = sum(1 for x in range(N) if (T[x] == T[:, x]).all())
    return (tuple(sorted(collections.Counter(ords).items())), cen)
factors = {}
for N in range(127, 141):
    for p in range(2, N):
        if N % p:
            continue
        q = N // p
        for A in ([f"cyc {p}"] + ([f"dih {p//2}"] if p % 2 == 0 else [])):
            for B in ([f"cyc {q}"] + ([f"dih {q//2}"] if q % 2 == 0 else [])):
                if A.startswith("cyc") and B.startswith("cyc"):
                    continue  # abelian
                factors.setdefault(N, []).append(f"{A} x {B}")
seen = set(); out = []
for N, specs in sorted(factors.items()):
    for s in specs:
        T = groups.table(s)
        assert len(T) == N, (s, len(T))
        key = inv(T)
        if key in seen:
            continue
        seen.add(key)
        name = s.replace(" ", "_").replace("x", "X")
        path = f"bins/{N}_{name}.bin"
        groups.write_bin(T, path)
        out.append(f"{N} {path} {key[1]} :: {s}")
print("\n".join(out))
print(len(out), file=sys.stderr)
