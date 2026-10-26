# Exhaustive k=3 orbit family for Haar graphs H(G,S), D=7, |S|=5.
# S = {e, t} + one alpha-orbit {x, ax, a^2x} (size 3), t in Fix(alpha).  G = Base x A, alpha = conj(c) x M.
# usage: fam.py BASE MODS(e.g. 2,2,7 or 13 or 3,9) [maxM]
import itertools, sys, time
import numpy as np
D = 7

def perm_mul(p, q): return tuple(p[i] for i in q)            # p o q
def perm_inv(p):
    r = [0]*len(p)
    for i, x in enumerate(p): r[x] = i
    return tuple(r)

def base_group(name):
    els = list(itertools.permutations(range(5)))
    if name == 'A5':
        def even(p): return sum(1 for i in range(5) for j in range(i+1, 5) if p[i] > p[j]) % 2 == 0
        els = [p for p in els if even(p)]
    return els

def find_c(base):
    e = tuple(range(5))
    for p in base:
        if p != e and perm_mul(p, p) != e and perm_mul(perm_mul(p, p), p) == e: return p   # order 3
    return None

def apply_map(M, a, mods):
    r = [0]*len(mods)
    for c_, img in zip(a, M):
        for i in range(len(mods)): r[i] = (r[i] + c_*img[i]) % mods[i]
    return tuple(r)

def abelian_order3_autos(mods):
    """Endomorphisms of A=prod Z_m given by generator images, bijective, M^3 = 1, M != 1."""
    allel = list(itertools.product(*[range(m) for m in mods]))
    res = []
    for imgs in itertools.product(allel, repeat=len(mods)):
        if any(tuple(0 for _ in mods) != tuple((m*x) % mm for x, mm in zip(im, mods)) for m, im in zip(mods, imgs)
               ) and False: pass
        # image of generator i must have order dividing m_i
        ok = True
        for i, im in enumerate(imgs):
            if any((mods[i]*im[j]) % mods[j] for j in range(len(mods))): ok = False; break
        if not ok: continue
        img_set = {apply_map(imgs, a, mods) for a in allel}
        if len(img_set) != len(allel): continue
        if any(apply_map(imgs, apply_map(imgs, apply_map(imgs, a, mods), mods), mods) != a for a in allel): continue
        if all(apply_map(imgs, a, mods) == a for a in allel): continue
        res.append(imgs)
    return res, allel

def build(base, c, mods, Mimgs, allel):
    nA = len(allel); nB = len(base)
    bidx = {p: i for i, p in enumerate(base)}
    aidx = {a: i for i, a in enumerate(allel)}
    bm = np.empty((nB, nB), dtype=np.int32)
    for i, p in enumerate(base):
        for j, q in enumerate(base): bm[i, j] = bidx[perm_mul(p, q)]
    am = np.empty((nA, nA), dtype=np.int32)
    for i, a in enumerate(allel):
        for j, b in enumerate(allel):
            am[i, j] = aidx[tuple((x+y) % m for x, y, m in zip(a, b, mods))]
    N = nB * nA
    P = np.repeat(np.arange(nB), nA); Aa = np.tile(np.arange(nA), nB)
    mul = np.empty((N, N), dtype=np.int32)
    for i in range(N): mul[i, :] = bm[P[i]][P] * nA + am[Aa[i]][Aa]
    cinv = perm_inv(c)
    alpha = np.empty(N, dtype=np.int32)
    for i in range(N):
        p, a = base[P[i]], allel[Aa[i]]
        cp = perm_mul(perm_mul(c, p), cinv)
        alpha[i] = bidx[cp] * nA + aidx[apply_map(Mimgs, a, mods)]
    e = bidx[tuple(range(5))] * nA + aidx[tuple(0 for _ in mods)]
    return N, mul, alpha, e

def ecc_ok(N, mul, S, invS, e):
    for side in (0, 1):
        rA = np.zeros(N, bool); rB = np.zeros(N, bool)
        if side == 0: rA[e] = True
        else: rB[e] = True
        frA = np.nonzero(rA)[0]; frB = np.nonzero(rB)[0]
        for _ in range(D):
            nB_ = np.zeros(N, bool); nA_ = np.zeros(N, bool)
            for s in S:
                if frA.size: nB_[mul[s][frA]] = True
            for si in invS:
                if frB.size: nA_[mul[si][frB]] = True
            nB_ &= ~rB; nA_ &= ~rA
            rB |= nB_; rA |= nA_
            frA = np.nonzero(nA_)[0]; frB = np.nonzero(nB_)[0]
        if not (rA.all() and rB.all()): return False
    return True

def family(N, mul, alpha, e):
    fix = np.nonzero(alpha == np.arange(N))[0]
    fixset = set(fix.tolist())
    # orbits of size 3 off the fixed set
    seen = set(); orbits = []
    for x in range(N):
        if x in fixset or x in seen: continue
        o = [x, int(alpha[x]), int(alpha[alpha[x]])]
        if len(set(o)) != 3 or int(alpha[o[2]]) != x: continue
        for y in o: seen.add(y)
        orbits.append(o)
    return fix, orbits

def inverses(N, mul, e):
    inv = np.empty(N, dtype=np.int64)
    r, c_ = np.nonzero(mul == e)
    inv[r] = c_
    return inv

def search(base_name, mods, maxM=2, verbose=True):
    base = base_group(base_name); c = find_c(base)
    Ms, allel = abelian_order3_autos(mods)
    fixA = [sum(1 for a in allel if apply_map(M, a, mods) == a) for M in Ms]
    order = sorted(range(len(Ms)), key=lambda i: fixA[i])[:maxM]
    found = []
    for mi in order:
        Mimgs = Ms[mi]
        N, mul, alpha, e = build(base, c, mods, Mimgs, allel)
        fix, orbits = family(N, mul, alpha, e)
        inv = inverses(N, mul, e)
        ntried = 0; hit = None
        for t in fix:
            if t == e: continue
            for o in orbits:
                S = [e, int(t)] + o
                if len(set(S)) != 5: continue
                ntried += 1
                invS = [int(inv[s]) for s in S]
                if ecc_ok(N, mul, S, invS, e):
                    hit = S; break
            if hit: break
        if verbose:
            print(f"base={base_name} mods={mods} N={N} M={Mimgs} fixA={fixA[mi]} |Fix(alpha)|={len(fix)} orbits={len(orbits)} tried={ntried} HIT={hit}", flush=True)
        if hit: found.append((Mimgs, hit)); break
    return found

if __name__ == '__main__':
    base_name = sys.argv[1]; mods = tuple(int(x) for x in sys.argv[2].split(','))
    maxM = int(sys.argv[3]) if len(sys.argv) > 3 else 2
    t0 = time.time(); res = search(base_name, mods, maxM)
    print("done", round(time.time()-t0, 1), "s", "FOUND" if res else "none")
