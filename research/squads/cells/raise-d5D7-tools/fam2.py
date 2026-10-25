# Generalized exhaustive k=3 orbit-family search: base = permutation group (closure of generators), G = base x A.
import itertools, sys, time
import numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from fam import perm_mul, perm_inv, apply_map, abelian_order3_autos, ecc_ok, family, inverses, D

def closure(gens):
    n = len(gens[0]); e = tuple(range(n))
    els = {e}; frontier = [e]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = perm_mul(g, x)
                if y not in els: els.add(y); nxt.append(y)
        frontier = nxt
    return sorted(els)

def order3_reps(base):
    e = tuple(range(len(base[0])))
    o3 = [p for p in base if p != e and perm_mul(perm_mul(p, p), p) == e]
    # one representative per conjugacy class (cheap: keep distinct conjugates by orbit under base)
    seen = set(); reps = []
    for p in o3:
        if p in seen: continue
        reps.append(p)
        for g in base: seen.add(perm_mul(perm_mul(g, p), perm_inv(g)))
    return reps

def build(base, c, mods, Mimgs, allel):
    nA = len(allel); nB = len(base); nd = len(base[0])
    bidx = {p: i for i, p in enumerate(base)}; aidx = {a: i for i, a in enumerate(allel)}
    bm = np.empty((nB, nB), dtype=np.int32)
    for i, p in enumerate(base):
        for j, q in enumerate(base): bm[i, j] = bidx[perm_mul(p, q)]
    am = np.empty((nA, nA), dtype=np.int32)
    for i, a in enumerate(allel):
        for j, b in enumerate(allel): am[i, j] = aidx[tuple((x+y) % m for x, y, m in zip(a, b, mods))]
    N = nB * nA
    P = np.repeat(np.arange(nB), nA); Aa = np.tile(np.arange(nA), nB)
    mul = np.empty((N, N), dtype=np.int32)
    for i in range(N): mul[i, :] = bm[P[i]][P] * nA + am[Aa[i]][Aa]
    cinv = perm_inv(c)
    conj = {p: bidx[perm_mul(perm_mul(c, p), cinv)] for p in base}
    Mimg = {a: aidx[apply_map(Mimgs, a, mods)] for a in allel}
    alpha = np.array([conj[base[P[i]]] * nA + Mimg[allel[Aa[i]]] for i in range(N)], dtype=np.int32)
    e = bidx[tuple(range(nd))] * nA + aidx[tuple(0 for _ in mods)]
    return N, mul, alpha, e

def search(name, base, mods, maxM=3, maxc=3):
    Ms, allel = abelian_order3_autos(mods) if mods else ([()], [()])
    if not Ms: Ms = []
    if not mods: Ms = [()]
    fixA = [sum(1 for a in allel if apply_map(M, a, mods) == a) for M in Ms] if mods else [0]
    order = sorted(range(len(Ms)), key=lambda i: fixA[i])[:maxM]
    if not Ms: print(f"{name} mods={mods}: no order-3 automorphism of A", flush=True); return None
    cs = order3_reps(base)[:maxc]
    best = None
    for c in cs:
        for mi in order:
            N, mul, alpha, e = build(base, c, mods, Ms[mi], allel)
            fix, orbits = family(N, mul, alpha, e)
            if len(fix) > 20:
                print(f'{name} mods={mods} N={N} M={Ms[mi]} |Fix|={len(fix)} SKIPPED', flush=True); continue
            inv = inverses(N, mul, e)
            tried = 0; hit = None
            for t in fix:
                if t == e: continue
                for o in orbits:
                    S = [e, int(t)] + o
                    if len(set(S)) != 5: continue
                    tried += 1
                    if ecc_ok(N, mul, S, [int(inv[s]) for s in S], e): hit = S; break
                if hit: break
            print(f"{name} mods={mods} N={N} c={c[:6]}.. M={Ms[mi]} fixA={fixA[mi]} |Fix|={len(fix)} orbits={len(orbits)} tried={tried} HIT={hit}", flush=True)
            if hit: return (name, mods, Ms[mi], hit)
    return None
