"""Stabiliser of the 756 set: matrices from the dreadnaut generators of its vector graph (aut/g756.dre), then the
elements that preserve the hexagon (G2(11)).  Product-replacement sampling."""
import numpy as np, sys, re, random
sys.path.insert(0, '.'); sys.path.insert(0, '../ovoid')
from hexmod import Hex
import ovlib as L
SP = '/tmp/claude-0/-home-user-degree-diameter/0a251e0c-8f17-58ce-a4f2-34eda2ea0db1/scratchpad/'
q = 11
X = np.loadtxt('/home/user/degree-diameter/research/d13D7/sets/R756_r4c1_coords.txt', dtype=np.int64, comments='#') % q
n = len(X)
txt = open(SP + 'aut/g756.out').read().splitlines()
gens, cur = [], None
for line in txt:
    if line.startswith('('):
        if cur is not None: gens.append(cur)
        cur = line
    elif line.startswith(' ') and cur is not None and '(' in line or (cur is not None and line[:1].isdigit() is False and line.strip()[:1].isdigit()):
        cur += ' ' + line
    else:
        if cur is not None: gens.append(cur); cur = None
if cur is not None: gens.append(cur)
perms = []
for g in gens:
    p = list(range(11 * n))
    for cyc in re.findall(r'\(([^)]*)\)', g):
        e = [int(v) for v in cyc.split()]
        for i in range(len(e)): p[e[i]] = e[(i + 1) % len(e)]
    perms.append(p)
print('generators parsed:', len(perms))
def vec(u):
    x, lam = divmod(u, 10); return (X[x] * (lam + 1)) % q
# 7 independent vectors
basis = []; bi = []
for x in range(n):
    M = np.array(basis + [X[x]])
    if L._rank(M.tolist(), q) == len(M): basis.append(X[x]); bi.append(x)
    if len(basis) == 7: break
V = np.array(basis).T
Vi = np.array(L.mat_inv(V.tolist(), q))
mats = []
for p in perms:
    W = np.array([vec(p[x * 10]) for x in bi]).T
    M = (W @ Vi) % q
    # verify on all vectors
    ok = all(np.array_equal((M @ vec(u)) % q, vec(p[u])) for u in range(0, 10 * n, 7))
    assert ok, 'generator is not linear'
    mats.append(M)
print('all generators linear; isometries:', [L.is_isometry(M.tolist(), L.std_gram(q), q) for M in mats])
H = Hex(SP + 'hex_q11.bin')
rng = random.Random(1)
test_lines = [rng.randrange(H.N) for _ in range(40)]
def in_G2(M):
    for l in test_lines:
        pts = H.X[H.lp[l]]
        img = H.index_of((M @ pts.T).T % q)
        cand = set(H.pl[img[0]].tolist())
        for p in img[1:]: cand &= set(H.pl[p].tolist())
        if not cand: return False
    return True
print('generators in G2(11):', [in_G2(M) for M in mats])
# product replacement
state = [m.copy() for m in mats] + [m.copy() for m in mats]
found = []
for it in range(6000):
    i, j = rng.sample(range(len(state)), 2)
    state[i] = (state[i] @ state[j]) % q if rng.random() < 0.5 else (state[j] @ state[i]) % q
    M = state[i]
    if in_G2(M):
        found.append(M.copy())
print('random elements in G2(11):', len(found), 'of 6000')
np.save(SP + 'stab756_mats.npy', np.array(mats))
if found: np.save(SP + 'stab756_g2.npy', np.array(found))
