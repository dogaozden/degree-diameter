# gen_phi.py GROUPS gid OUTDIR: writes every involutory automorphism (phi^2 = id, phi != id) of the group as N ints,
# plus prints the multiplier k when the group is cyclic (phi(g) = g^k for a generator g).
import sys, os
path, want, outdir = sys.argv[1], int(sys.argv[2]), sys.argv[3]
tok = open(path).read().split()
i = 0; M = None
while i < len(tok):
    if tok[i] == 'G':
        N, gid = int(tok[i+1]), int(tok[i+2]); name = tok[i+3]; i += 4
        vals = list(map(int, tok[i:i+N*N])); i += N*N
        if gid == want:
            M = [vals[r*N:(r+1)*N] for r in range(N)]; break
    else:
        i += 1
assert M is not None, "group not found"
def closure(gens):
    S = {0}; q = [0]
    while q:
        e = q.pop()
        for g in gens:
            x = M[e][g]
            if x not in S: S.add(x); q.append(x)
    return S
def order(x):
    o, y = 1, x
    while y != 0: y = M[y][x]; o += 1
    return o
gens = []
for x in range(1, N):
    if x not in closure(gens): gens.append(x)
print("N", N, "gid", gid, "name", name, "gens", gens, "orders", [order(g) for g in gens])
def build(imgs):
    phi = {0: 0}; q = [0]
    while q:
        e = q.pop()
        for g, h in zip(gens, imgs):
            t = M[e][g]; v = M[phi[e]][h]
            if t in phi:
                if phi[t] != v: return None
            else:
                phi[t] = v; q.append(t)
    if len(phi) != N or len(set(phi.values())) != N: return None
    for a in range(N):
        for b in range(N):
            if phi[M[a][b]] != M[phi[a]][phi[b]]: return None
    return [phi[a] for a in range(N)]
import itertools
found = []
for imgs in itertools.product(range(N), repeat=len(gens)):
    if any(order(h) != order(g) for g, h in zip(gens, imgs)): continue
    phi = build(imgs)
    if phi is None: continue
    if any(phi[phi[a]] != a for a in range(N)): continue
    found.append(phi)
os.makedirs(outdir, exist_ok=True)
for idx, phi in enumerate(found):
    fn = os.path.join(outdir, "phi_%d_%d_%d.txt" % (N, gid, idx))
    open(fn, "w").write(" ".join(map(str, phi)) + "\n")
    label = ""
    if len(gens) == 1:
        g = gens[0]; y = g; k = 1
        while y != phi[g]:
            y = M[y][g]; k += 1
        label = "multiplier k=%d" % k
    print("aut", idx, "file", fn, "identity" if all(phi[a] == a for a in range(N)) else "nontrivial", label)
