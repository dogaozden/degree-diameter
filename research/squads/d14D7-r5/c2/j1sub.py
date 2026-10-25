#!/usr/bin/env python3
"""c2: find subgroups of J1 (orders ~6..200) as explicit generator sets, write them to subgroups/.
Parents: cyclic groups of each element-order class, their centralizers and normalizers, C(involution),
N(Sylow-2) = 2^3:7:3. Subgroups: 2-generated subgroups <a,b> with b in N(<a>) or C(a) inside a parent."""
import sys, os, random, time, json
import numpy as np
sys.path.insert(0, '/home/user/degree-diameter/research/squads/d14D7-r5/c2')
import j1lib as J
from j1lib import mm, key, I7, closure, order_of, set_normalizer_mask
import ovlib as L

HERE = J.HERE
SUB = os.path.join(HERE, 'subgroups')
os.makedirs(SUB, exist_ok=True)
rng = random.Random(7)
t0 = time.time()
ALL = np.load(os.path.join(HERE, 'j1_all_u8.npy')).astype(np.int64)
N = len(ALL)
ORD = np.zeros(N, dtype=np.int64)
X = ALL.copy()
Iflat = I7.reshape(49)
for k in range(1, 40):
    done = np.all(X.reshape(N, 49) == Iflat, axis=1)
    newly = done & (ORD == 0)
    ORD[newly] = k
    if np.all(ORD > 0): break
    X = mm(X, ALL)
vals, cnts = np.unique(ORD, return_counts=True)
print('element orders:', dict(zip(vals.tolist(), cnts.tolist())), '[%.1fs]' % (time.time() - t0), flush=True)

def fingerprint(x):
    pw = [I7]
    for _ in range(6): pw.append(mm(pw[-1], x))
    return tuple(int(np.trace(pw[k]) % J.Q) for k in range(1, 7))

def mask_norm(H, x, k1=False):
    """boolean mask over the array H of g with g x g^-1 in <x> (k1: centralizer)."""
    o = order_of(x)
    pw = [I7]
    for _ in range(1, o): pw.append(mm(pw[-1], x))
    gx = mm(H, x)
    m = np.zeros(len(H), bool)
    for k in ([1] if k1 else range(o)):
        m |= np.all((gx == mm(pw[k], H)).reshape(len(H), 49), axis=1)
    return m

def inv_hist(elems):
    h = {}
    for M in elems:
        o = order_of(M); h[o] = h.get(o, 0) + 1
    return tuple(sorted(h.items()))

parents = []   # (name, array of elements, generators)
reps = {}
for n in vals.tolist():
    if n == 1: continue
    idx = np.nonzero(ORD == n)[0]
    samp = [int(i) for i in rng.sample(list(idx), min(60, len(idx)))]
    fps = {}
    for i in samp:
        fp = fingerprint(ALL[i])
        fps.setdefault(fp, i)
    for fp, i in list(fps.items())[:4]:
        reps.setdefault(n, []).append((fp, i))
print('representative fingerprints per order:', {n: len(v) for n, v in reps.items()}, flush=True)

def add_parent(name, arr, gens):
    parents.append((name, arr, gens))
    print('parent', name, 'size', len(arr), 'hist', inv_hist(arr) if len(arr) <= 700 else '-', '[%.1fs]' % (time.time() - t0), flush=True)

for n in sorted(reps):
    if n not in (2, 3, 5, 6, 7, 10, 11, 15, 19, 20, 21, 4, 8, 9, 12, 14, 18):
        continue
    for j, (fp, i) in enumerate(reps[n]):
        x = ALL[i]
        cyc = closure([x])
        add_parent(f'Z{n}_{j}', np.array(list(cyc.values())), [x])
        mC = mask_norm(ALL, x, k1=True)
        C = ALL[mC]
        if len(C) <= 700:
            cg = J.small_gens({key(M): M for M in C}, rng)
            if cg is not None: add_parent(f'C{n}_{j}', C, cg)
        mN = mask_norm(ALL, x)
        Nn = ALL[mN]
        if len(Nn) <= 700 and len(Nn) > len(C):
            ng = J.small_gens({key(M): M for M in Nn}, rng)
            if ng is not None: add_parent(f'N{n}_{j}', Nn, ng)

# Sylow-2 normaliser (2^3:7:3 expected, order 168)
inv_reps = [i for fp, i in reps.get(2, [])]
x2 = ALL[inv_reps[0]]
Cx = ALL[mask_norm(ALL, x2, k1=True)]
invs = [M for M in Cx if np.array_equal(mm(M, M), I7) and not np.array_equal(M, I7)]
P = None
for _ in range(2000):
    y = invs[rng.randrange(len(invs))]
    if np.array_equal(y, x2): continue
    zs = [z for z in invs if not np.array_equal(mm(y, z), z @ y % 11 * 0 + mm(y, z)) ]  # placeholder
    z = invs[rng.randrange(len(invs))]
    if np.array_equal(z, x2) or np.array_equal(z, y): continue
    if not np.array_equal(mm(y, z), mm(z, y)): continue
    Pd = closure([x2, y, z])
    if len(Pd) == 8:
        P = (Pd, [x2, y, z]); break
if P is not None:
    Pd, Pg = P
    mask = set_normalizer_mask(ALL, Pd, Pg)
    NP = ALL[mask]
    print('Sylow-2 P size', len(Pd), 'N(P) size', len(NP), flush=True)
    add_parent('N2P_8', NP, J.small_gens({key(M): M for M in NP}, rng))
    add_parent('P2_8', np.array(list(Pd.values())), Pg)
    add_parent('C2_inv', Cx, J.small_gens({key(M): M for M in Cx}, rng))

# subgroups: <a,b> with b in N_H(<a>) or C_H(a), inside each parent
found = {}   # invariant -> entry
def record(name_parent, gens, size, hist):
    inv = (size, hist)
    if inv in found: return
    found[inv] = dict(parent=name_parent, gens=gens, size=size, hist=hist)

for name, H, Hg in parents:
    if len(H) < 6: continue
    for _ in range(40):
        a = H[rng.randrange(len(H))]
        oa = order_of(a)
        if oa == 1: continue
        NHa = H[mask_norm(H, a)]
        CHa = H[mask_norm(H, a, k1=True)]
        for pool in (NHa, CHa):
            for _ in range(3):
                b = pool[rng.randrange(len(pool))]
                G = closure([a, b], cap=200)
                if G is None or len(G) < 6: continue
                # check subgroup of H
                Hd = {key(M) for M in H}
                if not all(k in Hd for k in G): continue
                size = len(G)
                hist = inv_hist(list(G.values()))
                record(name, [a, b], size, hist)
print('distinct subgroups (size,hist) found:', len(found), '[%.1fs]' % (time.time() - t0), flush=True)

# add the parents themselves (small ones) and write files
entries = []
for name, H, Hg in parents:
    if len(H) > 200 and len(H) != 660: continue
    if len(H) < 6: continue
    hist = inv_hist(H) if len(H) <= 700 else None
    entries.append(dict(name=name, size=len(H), hist=hist, gens=Hg, parent='self'))
for inv, e in found.items():
    entries.append(dict(name=f"S{e['size']}_{e['parent']}", size=e['size'], hist=e['hist'], gens=e['gens'], parent=e['parent']))
# dedupe by (size, hist)
seen = {}
for e in entries:
    k = (e['size'], e['hist'])
    if k in seen: continue
    seen[k] = e
final = sorted(seen.values(), key=lambda e: (e['size'], str(e['hist'])))
manifest = []
for j, e in enumerate(final):
    fn = os.path.join(SUB, f"g{j:02d}_{e['size']}_{e['name']}.txt")
    L.write_gens(fn, [np.asarray(g).tolist() for g in e['gens']], f"J1 subgroup order {e['size']} from {e['name']} parent {e['parent']}")
    manifest.append(dict(file=fn, size=e['size'], hist=str(e['hist']), parent=e['parent'], name=e['name']))
json.dump(manifest, open(os.path.join(SUB, 'manifest.json'), 'w'), indent=1)
for m in manifest: print(m['size'], os.path.basename(m['file']), m['hist'][:120])
print('total subgroup candidates', len(manifest), '[%.1fs]' % (time.time() - t0))
