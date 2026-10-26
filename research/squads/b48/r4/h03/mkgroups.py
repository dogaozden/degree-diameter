# h03: enumerate metacyclic groups (split and non-split) of orders 217..230, dedupe by an invariant signature,
# write each representative as a groups.py .bin table, plus the abc and D5xD11 groups.
import sys, os, math, random
import numpy as np
from collections import Counter
sys.path.insert(0, '/home/user/degree-diameter/research/squads/b48/tools')
import groups as G
OUT = '/home/user/degree-diameter/research/squads/b48/r4/h03/groups'
os.makedirs(OUT, exist_ok=True)
random.seed(1)

def meta_table(m, k, r, t):
    N = m * k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    g = np.arange(N); gi = g % m; gj = g // m
    I = gi[:, None]; J = gj[:, None]; P = gi[None, :]; Q = gj[None, :]
    s = J + Q; carry = (s >= k).astype(np.int64); jj = s % k
    ii = (I + rp[J] * P + t * carry) % m
    return (ii + m * jj).astype(np.int64)

def assoc_ok(T, samples=3000):
    N = T.shape[0]
    a = np.random.randint(0, N, samples); b = np.random.randint(0, N, samples); c = np.random.randint(0, N, samples)
    return bool((T[T[a, b], c] == T[a, T[b, c]]).all()) and bool((T[0] == np.arange(N)).all()) and bool((T[:, 0] == np.arange(N)).all())

def signature(T):
    N = T.shape[0]
    g = np.arange(N)
    inv = np.array([int(np.where(T[x] == 0)[0][0]) for x in range(N)])
    ordr = np.zeros(N, dtype=np.int64); cur = g.copy()
    for step in range(1, N + 1):
        mask = (cur == 0) & (ordr == 0)
        ordr[mask] = step
        if (ordr > 0).all(): break
        cur = T[cur, g]
    C = T[T, inv[:, None]]            # C[x,g] = x g x^-1
    csz = np.array([len(np.unique(C[:, h])) for h in range(N)])
    XY = T; XYX = T[XY, inv[:, None]]; comm = T[XYX, inv[None, :]]
    ncomm = len(np.unique(comm))
    pairs = Counter(zip(ordr.tolist(), csz.tolist()))
    ncls = len(np.unique(C.min(axis=0)))
    center = int((csz == 1).sum())
    return (N, tuple(sorted(pairs.items())), ncls, ncomm, center), inv

def divisors(n):
    return [d for d in range(1, n + 1) if n % d == 0]

cands = []
for N in range(217, 231):
    seen = {}
    nonab = 0
    for m in divisors(N):
        k = N // m
        if m < 2 or k < 2: continue
        for r in range(2, m):
            if math.gcd(r, m) != 1 or pow(r, k, m) != 1 % m: continue
            for t in range(m):
                if (t * (r - 1)) % m != 0: continue
                T = meta_table(m, k, r, t)
                if not assoc_ok(T): continue
                if (T == T.T).all(): continue          # abelian
                sig, inv = signature(T)
                if sig in seen: continue
                seen[sig] = (m, k, r, t)
                cands.append((N, f"meta {m} {k} {r} {t}", T))
    print(f"N={N}: {len(seen)} distinct nonabelian metacyclic signatures", file=sys.stderr)

# D5 x D11 (order 220, not metacyclic in general) and the abc group from abc.py
def dihedral_table(n):
    return G.table(f"dih {n}").astype(np.int64)
def product_table(A, B):
    na, nb = A.shape[0], B.shape[0]
    T = np.zeros((na * nb, na * nb), dtype=np.int64)
    ia = np.arange(na * nb) // nb; ib = np.arange(na * nb) % nb
    T = (A[ia[:, None], ia[None, :]] * nb + B[ib[:, None], ib[None, :]]).astype(np.int64)
    return T
D5 = dihedral_table(5); D11 = dihedral_table(11)
TD = product_table(D5, D11)
assert assoc_ok(TD)
sig, _ = signature(TD); cands.append((220, "D5xD11", TD))
import subprocess
out = subprocess.run([sys.executable, '/home/user/degree-diameter/research/squads/b48/tools/abc.py', 'list', '217', '230', '--nonmeta'], capture_output=True, text=True).stdout
print("abc list:", out.strip(), file=sys.stderr)
for line in out.strip().splitlines():
    parts = line.split()
    if len(parts) < 3: continue
    k, comps, order = parts[0], parts[1], int(parts[2])
    tb = f"{OUT}/abc_{k}_{comps.replace(':','-').replace(',','_')}.bin"
    subprocess.run([sys.executable, '/home/user/degree-diameter/research/squads/b48/tools/abc.py', 'build', f"{k} {comps}", tb], check=True)
    T = np.fromfile(tb, dtype=np.int32, count=1)
    N = int(T[0]); tab = np.fromfile(tb, dtype=np.uint16, offset=4).reshape(N, N).astype(np.int64)
    assert assoc_ok(tab)
    sg, _ = signature(tab)
    if any(sg == s for (_, _, s) in []): pass
    cands.append((N, f"abc {k} {comps}", tab))

# write representatives
index = []
bysig = {}
for N, name, T in cands:
    sg, inv = signature(T)
    if sg in bysig: continue
    bysig[sg] = name
    fn = f"{OUT}/g{N}_{len(index):03d}.bin"
    with open(fn, 'wb') as f:
        np.array([N], dtype=np.int32).tofile(f)
        T.astype(np.uint16).tofile(f)
    index.append((N, name, fn))
with open('/home/user/degree-diameter/research/squads/b48/r4/h03/index.txt', 'w') as f:
    for N, name, fn in index:
        f.write(f"{N} {name} {fn}\n")
print(len(index), "groups written", file=sys.stderr)
