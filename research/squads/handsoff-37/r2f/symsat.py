#!/usr/bin/env python3
"""r2f: SAT search for cyclic lifts (Z_m voltage graphs on cubic bipartite base k+k) that are invariant under an extra
automorphism s = (sigma, alpha): lifted s(u,h) = (sigma u, alpha h). Base edge (a,b,t) (a in A, b in B, lift edge
(a,h)-(b,h+t)) is present iff (sigma a, sigma b, alpha t) is present. Sources of the walk/coverage constraints are
reduced to sigma-orbit representatives (s maps (u,0) to (sigma u,0)).
usage: symsat.py M K D ALPHA SIGMA_A SIGMA_B OUT [solver]
  SIGMA_A / SIGMA_B: cycle lengths of sigma on the A / B base vertices, e.g. "1,1,1,3,3,3" (fixed points first).
Writes the lift edge list to OUT if SAT (vertex (u,h) = u*M+h, A = u < K, B = K..2K-1)."""
import sys, time, itertools, os
from pysat.formula import IDPool
from pysat.card import CardEnc, EncType
from pysat.solvers import Solver


def sigma_from_cycles(cyc_str, offset):
    lens = [int(x) for x in cyc_str.split(',') if x.strip()]
    sig = []
    pos = offset
    cycles = []
    for L in lens:
        cyc = list(range(pos, pos + L))
        cycles.append(cyc)
        pos += L
    perm = [0] * pos
    for c in cycles:
        for i, x in enumerate(c):
            perm[x] = c[(i + 1) % len(c)]
    return perm, pos - offset


def main():
    m, k, D = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    alpha = int(sys.argv[4]) % m
    cA, cB, outf = sys.argv[5], sys.argv[6], sys.argv[7]
    sname = sys.argv[8] if len(sys.argv) > 8 else 'cadical195'
    permA, nA = sigma_from_cycles(cA, 0)
    permB, nB = sigma_from_cycles(cB, 0)
    assert nA == k and nB == k, (nA, nB, k)
    sig = [0] * (2 * k)
    for i in range(k):
        sig[i] = permA[i]
        sig[k + i] = k + permB[i]
    import os
    FIX = os.environ.get('FIXBASE')  # sanity check: pin a known base (file from base_f21.py) and expect SAT
    fixed_base = None
    if FIX:
        tok = open(FIX).read().split('\n')
        kk = int(tok[0].split()[1]); rr = int(tok[1].split()[1])
        assert kk == k and rr == alpha, (kk, rr)
        sig = [int(x) for x in tok[2].split()[1:]]
        fixed_base = set()
        for line in tok[3:]:
            if line.strip():
                a, b, t = map(int, line.split()); fixed_base.add((a, b, t))
    t0 = time.time()
    pool = IDPool()
    # raw variables E[a,b,t]
    E = {}
    for a in range(k):
        for b in range(k):
            for t in range(m):
                E[(a, b, t)] = pool.id(('E', a, b, t))
    clauses = []
    # symmetry: E[a,b,t] <-> E[sig a, sig b, alpha t]
    for a in range(k):
        for b in range(k):
            for t in range(m):
                x = E[(a, b, t)]
                y = E[(sig[a], sig[k + b] - k, (alpha * t) % m)]
                if x != y:
                    clauses.append([-x, y]); clauses.append([x, -y])
    if os.environ.get('G4', '0') == '1':
        # lift girth >= 6: no base 4-cycle a1-b1-a2-b2 with voltage sum t1-t2+t3-t4 = 0 (c3's clauses)
        for a1, a2 in itertools.combinations(range(k), 2):
            for b1, b2 in itertools.combinations(range(k), 2):
                for t1, t2, t3, t4 in itertools.product(range(m), repeat=4):
                    if (t1 - t2 + t3 - t4) % m == 0:
                        clauses.append([-E[(a1, b1, t1)], -E[(a2, b1, t2)], -E[(a2, b2, t3)], -E[(a1, b2, t4)]])
    # degrees
    for a in range(k):
        lits = [E[(a, b, t)] for b in range(k) for t in range(m)]
        clauses += CardEnc.equals(lits=lits, bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
    for b in range(k):
        lits = [E[(a, b, t)] for a in range(k) for t in range(m)]
        clauses += CardEnc.equals(lits=lits, bound=3, vpool=pool, encoding=EncType.seqcounter).clauses
    inc = {w: [] for w in range(2 * k)}
    for a in range(k):
        for b in range(k):
            for t in range(m):
                inc[a].append((b, t, E[(a, b, t)]))
                inc[k + b].append((a, t, E[(a, b, t)]))
    # sources: sigma-orbit representatives of base vertices (both sides)
    seen = set(); sources = []
    for u in range(2 * k):
        if u in seen: continue
        orb = [u]; x = sig[u]
        while x != u:
            orb.append(x); x = sig[x]
        seen.update(orb); sources.append(u)
    L = D - 1
    for src in sources:
        s_side = 0 if src < k else 1
        R = [dict() for _ in range(L + 1)]
        v0 = pool.id(('R', src, 0, src, 0))
        R[0][(src, 0)] = v0
        clauses.append([v0])
        for j in range(L):
            wit = {}
            for (w, g), rv in R[j].items():
                for (w2, t, ev) in inc[w]:
                    x2 = (k + w2, (g + t) % m) if w < k else (w2, (g - t) % m)
                    Wv = pool.id(('W', src, j, w, g, w2, t))
                    clauses.append([-Wv, rv]); clauses.append([-Wv, ev])
                    wit.setdefault(x2, []).append(Wv)
            for x2, ws in wit.items():
                rv2 = pool.id(('R', src, j + 1, x2[0], x2[1]))
                R[j + 1][x2] = rv2
                clauses.append([-rv2] + ws)
        for w in range(2 * k):
            if (w < k) != (src < k): continue
            for h in range(m):
                if w == src and h == 0: continue
                lits = [R[j][(w, h)] for j in range(2, L + 1, 2) if (w, h) in R[j]]
                clauses.append(lits)  # empty -> unsatisfiable
    print(f"built m={m} k={k} D={D} alpha={alpha} sigA={cA} sigB={cB} sources={len(sources)} vars={pool.top} "
          f"clauses={len(clauses)} in {time.time()-t0:.1f}s", flush=True)
    if fixed_base is not None:
        for key, v in E.items():
            clauses.append([v] if key in fixed_base else [-v])
    with Solver(name=sname, bootstrap_with=clauses) as S:
        t1 = time.time()
        ok = S.solve()
        print(f"RESULT {'SAT' if ok else 'UNSAT'} solver={sname} time={time.time()-t1:.1f}s", flush=True)
        if ok:
            mset = set(l for l in S.get_model() if l > 0)
            base = [(a, b, t) for (a, b, t), v in E.items() if v in mset]
            edges = []
            for a, b, t in base:
                for h in range(m):
                    edges.append((a * m + h, (k + b) * m + (h + t) % m))
            n = 2 * k * m
            with open(outf, 'w') as fh:
                fh.write(f"{n}\n" + ''.join(f"{x} {y}\n" for x, y in edges))
            print("BASE", ' '.join(f"{a}-{b}:{t}" for a, b, t in base), flush=True)
            print("wrote", outf, "n =", n, "edges", len(edges), flush=True)


if __name__ == '__main__':
    main()
