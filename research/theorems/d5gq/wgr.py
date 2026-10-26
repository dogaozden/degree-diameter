"""Whole-graph repair (Section 12 of D5_QUADRANGLE.md): extra freed points on the H->H arcs of the typed (13,5)-type
layout, repaired through third levels and hubs by annealing the non-friendly matchings.

Start: the configuration of build_relaxed.py (ovoid O on H->D, relaxed set T on D->H with the hub rule, two-point local
dualities on non-friendly arcs).  Then E extra random points are freed on every H->H arc (avoiding the local-duality
structure), hubs are added for the new slots, and the matchings of the non-friendly arcs are annealed with targeted
swaps until no pair (endpoint of a deleted non-friendly edge, vertex of the other level of its arc) is at distance > 5.
The bad pairs are counted by wgr_eval.c (bit-parallel BFS on the whole graph, hubs included).

usage: python3 wgr.py q T.json E seed iters out_prefix
"""
import sys, json, os, random, ctypes, time
import numpy as np
from gqlib import W, regular_spread_W
from levels import build, write_edges, apsp, rotational_arcs
from localdual import local_duality_pair, pick_pair
from repair import full_dist
from hubopt import hub_D0, search
from build_relaxed import partners

HERE = os.path.dirname(os.path.abspath(__file__))
so = os.path.join(HERE, 'wgr_eval.so')
if not os.path.exists(so) or os.path.getmtime(so) < os.path.getmtime(os.path.join(HERE, 'wgr_eval.c')):
    os.system('cc -O3 -march=native -shared -fPIC -o %s %s' % (so, os.path.join(HERE, 'wgr_eval.c')))
lib = ctypes.CDLL(so)
lib.wgr_bad.restype = ctypes.c_long
P32 = ctypes.POINTER(ctypes.c_int32)


def main():
    q = int(sys.argv[1]); T = sorted(json.load(open(sys.argv[2]))); E = int(sys.argv[3]); seed = int(sys.argv[4])
    iters = int(sys.argv[5]); out = sys.argv[6]
    rng = random.Random(seed)
    r = 3; types = 'HHHDHHD'; L = 7; arcs = rotational_arcs(L)
    Wq = W(q); G = Wq.dual(); N = G.np
    O = regular_spread_W(Wq); PT = partners(G, T, O)
    D = full_dist(G)
    M, R = {}, {}
    mutable = []
    for (u, v) in arcs:
        if types[u] != types[v]:
            M[(u, v)] = np.arange(N); R[(u, v)] = set(O) if types[u] == 'H' else set(T)
        else:
            Hq = G if types[u] == 'H' else Wq
            avoid = O if types[u] == 'H' else T
            x, y, l, m = pick_pair(Hq, avoid_pts=avoid)
            M[(u, v)] = np.array(local_duality_pair(Hq, x, y, l, m)); R[(u, v)] = {x, y}
            if types[u] == 'H':
                # D->D arcs stay fixed: every third-level route between levels 3 and 6 uses only friendly arcs, so
                # bad pairs there could not be repaired by moves; their local duality is repaired by Theorem C
                mutable.append((u, v))
            if types[u] == 'H' and E > 0:
                taboo = {x, y} | set(np.nonzero(Hq.col[x] | Hq.col[y])[0])
                cand = [p for p in range(N) if p not in taboo]
                R[(u, v)] |= set(rng.sample(cand, E))
    Minv = {t: np.argsort(M[t]) for t in arcs}
    # ---- slots and hubs (relaxed hub rule as in build_relaxed.py)
    Aslots = {j: [] for j in range(L)}; Bslots = {j: [] for j in range(L)}
    for (u, v) in arcs:
        for a in sorted(R[(u, v)]):
            Aslots[u].append((u, a, (u, v))); Bslots[v].append((v, int(M[(u, v)][a]), (u, v)))
    KB = min(len(Aslots[j]) for j in range(L)); KA = min(len(Bslots[j]) for j in range(L))
    Tof = {t: PT for t in arcs if types[t[0]] == 'D' and types[t[1]] == 'H'}
    hd_out = {j: next((u, v) for (u, v) in arcs if u == j and types[v] == 'D') for j in range(L) if types[j] == 'H'}
    Dlev = [j for j in range(L) if types[j] == 'D']; Hlev = [j for j in range(L) if types[j] == 'H']
    Bhubs = []; used = set(); fixedB = set(); fixedA = set()
    order = {}
    for d in Dlev:
        con = [s for s in Aslots[d] if s[2] in Tof and s[1] in Tof[s[2]]]
        order[d] = con + [s for s in Aslots[d] if s not in con]
    for i in range(KB):
        h = {}
        for d in Dlev:
            s = order[d][i]; h[d] = s
            if s[2] in Tof and s[1] in Tof[s[2]]:
                m, om = Tof[s[2]][s[1]]; jt = s[2][1]
                if jt in h:      # two constraints on the same level: keep the first, the second pair is left to routing
                    continue
                h[jt] = (jt, om, hd_out[jt])
                fixedB.add((i, d)); fixedB.add((i, jt))
        Bhubs.append(h)
    for h in Bhubs:
        for s in h.values():
            assert s not in used; used.add(s)
    for j in range(L):
        pool = [s for s in Aslots[j] if s not in used]
        for h in Bhubs:
            if j not in h: h[j] = pool.pop(0); used.add(h[j])
    groups = {d: {} for d in Dlev}
    for jp in Hlev:
        for s in Bslots[jp]:
            t = s[2]
            if t in Tof and s[1] in Tof[t]: groups[t[0]].setdefault(s[1], []).append(s)
    Ahubs = [dict() for _ in range(KA)]; usedB = set()
    for d in Dlev:
        for i, (l, slots) in enumerate(sorted(groups[d].items())):
            if i >= KA: break
            g = Ahubs[i]
            for s in slots: g[s[0]] = s; usedB.add(s); fixedA.add((i, s[0]))
            m, om = Tof[slots[0][2]][l]
            c = next(c for c in Bslots[d] if c[1] == om and c not in usedB); g[d] = c; usedB.add(c); fixedA.add((i, d))
    for j in range(L):
        pool = [s for s in Bslots[j] if s not in usedB]
        for g in Ahubs:
            if j not in g: g[j] = pool.pop(0); usedB.add(g[j])
    Bh = [[h[j] for j in range(L)] for h in Bhubs]; Ah = [[g[j] for j in range(L)] for g in Ahubs]
    if os.environ.get('RESUME'):
        import pickle
        st = pickle.load(open(os.environ['RESUME'], 'rb'))
        assert {t: sorted(v) for t, v in st['R'].items()} == {t: sorted(v) for t, v in R.items()}
        for t in arcs: M[t] = np.array(st['M'][t]); Minv[t] = np.argsort(M[t])
        Bh, Ah = st['Bh'], st['Ah']
        print('resumed from', os.environ['RESUME'])
    print('E=%d K_B=%d K_A=%d (order %d)' % (E, KB, KA, L * 2 * N + KB + KA)); sys.stdout.flush()
    delta = q - r
    Y = []          # the hub graph is chosen at the end (repairs must not depend on it)
    # ---- sources: endpoints of deleted non-friendly edges
    per = 2 * N
    def vid(j, kind, e): return j * per + (e if kind == 'P' else N + e)
    Ak = lambda t: 'P' if t == 'H' else 'L'; Bk = lambda t: 'L' if t == 'H' else 'P'
    src, tlev = [], []
    for t in mutable:
        u, v = t
        for x in sorted(R[t]):
            src.append(vid(u, Ak(types[u]), x)); tlev.append(v)
            src.append(vid(v, Bk(types[v]), int(M[t][x]))); tlev.append(u)
    nrel = 0
    for t, P in Tof.items():
        j, jp = t
        for l, (m, om) in P.items():
            hb = [h for h in Bh if h[j] == (j, l, t)]
            okB = bool(hb) and hb[0][jp][1] == om
            ha = [g for g in Ah if g[jp] == (jp, l, t)]
            okA = bool(ha) and ha[0][j][1] == om
            if not okB:
                src.append(vid(j, 'L', l)); tlev.append(jp); nrel += 1
            if not okA:
                src.append(vid(jp, 'L', l)); tlev.append(j); nrel += 1
    print('relaxed pairs left to routing: %d sources' % nrel)
    src = np.array(src, dtype=np.int32); tlev = np.array(tlev, dtype=np.int32)
    S = len(src)
    badc = np.zeros(S, dtype=np.int32); MAXB = 200000; badv = np.zeros(2 * MAXB, dtype=np.int32)

    def evaluate():
        # without the hub graph: repairs must not depend on Y (Y is chosen at the end and only adds paths)
        n, Ed = build(G, types, {t: list(M[t]) for t in arcs}, R, Bh, Ah, [], arcs=arcs, check_slots=False)
        Ed = np.array(Ed, dtype=np.int64)
        a = np.concatenate([Ed[:, 0], Ed[:, 1]]); b = np.concatenate([Ed[:, 1], Ed[:, 0]])
        o = np.argsort(a, kind='stable'); a = a[o]; b = b[o]
        cnt = np.bincount(a, minlength=n); DEG = int(cnt.max())
        start = np.concatenate([[0], np.cumsum(cnt)[:-1]])
        pos = np.arange(len(a)) - start[a]
        adj = -np.ones((n, DEG), dtype=np.int32); adj[a, pos] = b
        tot = lib.wgr_bad(n, DEG, adj.ctypes.data_as(P32), S, src.ctypes.data_as(P32), tlev.ctypes.data_as(P32),
                          per, 5, badc.ctypes.data_as(P32), badv.ctypes.data_as(P32), MAXB)
        nb = min(int(tot), MAXB)
        return int(tot), badv[:2 * nb].reshape(-1, 2).copy()

    def arc_between(i, j):
        return (i, j) if (i, j) in M else (j, i)

    def targeted_move(s_idx, v_vertex):
        """try to create a length-<=5 route from source src[s_idx] to v_vertex through a third level"""
        sv = int(src[s_idx]); j = sv // per; x = sv % per
        jp = v_vertex // per; vv = v_vertex % per
        if rng.random() < 0.5:           # symmetric: route from the target side
            j, jp, x, vv = jp, j, vv, x
        i = rng.choice([k for k in range(L) if k not in (j, jp)])
        t1 = arc_between(j, i); t2 = arc_between(i, jp)
        if t2 not in mutable:
            return None
        # entry into level i from x via t1 (fixed or mutable, used as is)
        ent = []
        if t1 == (j, i):
            kA = Ak(types[j]); offA = 0 if kA == 'P' else N
            for e in np.nonzero(D[x] <= 2)[0]:
                if (e >= N) == (kA == 'L') and (e - offA) not in R[t1]:
                    yb = int(M[t1][e - offA]); ent.append((int(D[x, e]), (0 if Bk(types[i]) == 'P' else N) + yb))
        else:
            kB = Bk(types[j]); offB = 0 if kB == 'P' else N
            for e in np.nonzero(D[x] <= 2)[0]:
                if (e >= N) == (kB == 'L'):
                    ya = int(Minv[t1][e - offB])
                    if ya not in R[t1]: ent.append((int(D[x, e]), (0 if Ak(types[i]) == 'P' else N) + ya))
        if not ent:
            return None
        d1, y = rng.choice(ent)
        budget = 3 - d1
        if t2 == (i, jp):   # z in A(level i), w in B(level jp): set M_t2[z] = w
            kz, kw = Ak(types[i]), Bk(types[jp])
        else:               # w in A(level jp), z in B(level i): set M_t2[w] = z
            kz, kw = Bk(types[i]), Ak(types[jp])
        oz = 0 if kz == 'P' else N; ow = 0 if kw == 'P' else N
        zs = [e for e in np.nonzero(D[y] <= budget)[0] if (e >= N) == (kz == 'L')]
        if not zs: return None
        z = int(rng.choice(zs)); d2 = int(D[y, z])
        ws = [e for e in np.nonzero(D[vv] <= budget - d2)[0] if (e >= N) == (kw == 'L')]
        if not ws: return None
        w = int(rng.choice(ws))
        zl, wl = z - oz, w - ow
        if t2 == (i, jp):
            if zl in R[t2]: return None
            z2 = int(Minv[t2][wl])
            if z2 in R[t2] or z2 == zl: return None
            return (t2, zl, z2)
        else:
            if wl in R[t2]: return None
            w2 = int(Minv[t2][zl])
            if w2 in R[t2] or w2 == wl: return None
            return (t2, wl, w2)

    def apply_swap(mv):
        t, a1, a2 = mv
        b1, b2 = M[t][a1], M[t][a2]
        M[t][a1], M[t][a2] = b2, b1
        Minv[t][b2], Minv[t][b1] = a1, a2

    def hub_move(s_idx, v_vertex):
        """move the slot, in the target level, of the hub sitting at the source so that it lies near the target"""
        sv = int(src[s_idx]); j = sv // per; x = sv % per; jp = v_vertex // per; vv = v_vertex % per
        isA = (x < N) == (Ak(types[j]) == 'P')        # source is an A-vertex (freed point of an arc out of j)
        hubs = Bh if isA else Ah; fixed = fixedB if isA else fixedA
        el = x if x < N else x - N
        cand = [i for i, sl in enumerate(hubs) if sl[j][1] == el and (i, jp) not in fixed]
        if not cand: return None
        i = rng.choice(cand)
        # target level slots of the same kind, close to vv
        others = [(k, sl[jp]) for k, sl in enumerate(hubs) if k != i and (k, jp) not in fixed]
        kind = Ak(types[jp]) if isA else Bk(types[jp]); off = 0 if kind == 'P' else N
        good = [(k, sl) for (k, sl) in others if D[sl[1] + off, vv] <= 3]
        if not good: return None
        k, sl = rng.choice(good)
        return (hubs, i, k, jp)

    def apply_hub(hm):
        hubs, i, k, jp = hm
        hubs[i][jp], hubs[k][jp] = hubs[k][jp], hubs[i][jp]

    import signal, pickle
    def save_state(*a):
        pickle.dump(dict(M={t: list(M[t]) for t in arcs}, R=R, Bh=Bh, Ah=Ah), open(out + '.state.pkl', 'wb'))
        if a:
            print('saved state on signal'); sys.stdout.flush(); sys.exit(1)
    signal.signal(signal.SIGTERM, save_state)
    cost, bad = evaluate(); print('initial bad pairs', cost); sys.stdout.flush()
    Ttemp = 2.0; t0 = time.time()
    for it in range(iters):
        if cost == 0: break
        k = rng.randrange(len(bad)); s_idx, vtx = int(bad[k, 0]), int(bad[k, 1])
        if rng.random() < float(os.environ.get('HUBMOVE', '0.3')):
            hm = hub_move(s_idx, vtx)
            if hm is None: continue
            apply_hub(hm)
            c2, bad2 = evaluate()
            if c2 <= cost or rng.random() < np.exp((cost - c2) / Ttemp):
                cost, bad = c2, bad2
            else:
                apply_hub(hm)
            continue
        mv = targeted_move(s_idx, vtx)
        if mv is None: continue
        apply_swap(mv)
        c2, bad2 = evaluate()
        if c2 <= cost or rng.random() < np.exp((cost - c2) / Ttemp):
            cost, bad = c2, bad2
        else:
            apply_swap(mv)
        Ttemp = max(0.3, Ttemp * 0.999)
        if it % 50 == 0:
            print('it %d bad %d (%.0fs)' % (it, cost, time.time() - t0)); sys.stdout.flush()
    print('final bad pairs (non-friendly endpoints)', cost)
    import pickle
    pickle.dump(dict(M={t: list(M[t]) for t in arcs}, R=R, Bh=Bh, Ah=Ah), open(out + '.state.pkl', 'wb'))
    if cost:
        return
    n0, E0 = build(G, types, {t: list(M[t]) for t in arcs}, R, Bh, Ah, [], arcs=arcs)
    nv = L * per
    D0 = hub_D0(n0, E0, list(range(nv, nv + KB + KA)))
    for sd in range(6):
        Y, hc = search(D0, KB, KA, delta, seed=sd, iters=6000)
        print('hub search', sd, hc)
        if hc == 0: break
    if hc:
        print('no hub graph satisfying (HG); not writing a graph'); return
    n, Ed = build(G, types, {t: list(M[t]) for t in arcs}, R, Bh, Ah, Y, arcs=arcs)
    write_edges(out + '.edges', n, Ed)
    json.dump(dict(q=q, r=r, types=types, arcs=arcs, ovoid_Q4=O, T=T, K_B=KB, K_A=KA, Bhub_slots=Bh, Ahub_slots=Ah,
                   Y=Y, nonfriendly={'%d,%d' % t: dict(R=sorted(R[t]), M=list(M[t])) for t in mutable},
                   W_points=[list(c) for c in Wq.coords], W_lines=[list(l) for l in Wq.lines]),
              open(out + '.json', 'w'), default=int)
    print(apsp(out + '.edges', q + 1 + r, 5, threads=2))


if __name__ == '__main__':
    main()
