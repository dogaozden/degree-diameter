#!/usr/bin/env python3
"""tmL_build.py: research/d15D7b/tm3_build.py (job cell-15-7) for any odd number of levels L = len(T) and any q
(job d7-family, 2026-10-25): r = (L-1)/2 matchings per class, max degree q+1+r, hub-graph degree q+1+r-L, vertex ids
(x, level j) = 2Nj + kind*N + x, line-side hubs 2NL + h, point-side hubs 2NL + KB + h. Used for (14,7) (H(11), HDHDH)
and (16,7) (H(13), HDHDH). Header line 'typedmirrorL'. The rest of this docstring is tm3_build's.

The typed L-level graph (research/squads/cells/d16D7.md) with
  - friendly transitions (types differ, identity matching) freeing per-transition sets that may contain collinear
    pairs of points / concurrent pairs of lines (relaxed surgery, research/d15D7b/RELAXED.md),
  - the mirrored surgery (sigma, R') on the nine non-friendly transitions (research/theorems/MIRRORED_SURGERY.md),
  - hubs with an explicit slot in every level, chosen so that every pair satisfies the relaxed condition (R2),
  - an explicit hub graph (degree <= 15 - 7 = 8).
Slots: every freed (transition t = j -> j2, element x) leaves an A-slot at (x, j) and a B-slot at (img(x), j2). Slot
lists per level in canonical order (transitions j -> j+1, j+2, j+3 for A-slots of level j; for B-slots of level j2 the
transitions in the order of the loop over j and k; inside a transition the freed ids sorted). A line-side hub (colour 1)
holds one A-slot per level, a point-side hub (colour 0) one B-slot per level.
Vertex ids: (x, level j) = 2Nj + kind*N + x (kind 0 = point of H, 1 = line); line-side hubs 14N + h, point-side hubs
14N + KB + h.  In H levels the A-class is the points, in H^D levels the lines.
modes:
  assign HEXBIN MIRROR_SOL SETSPEC SEED OUT.sol      choose hub slots (one matching per level for the pair conditions);
                                                     prints the pairs that could not be served (drop one end and rerun)
  sethub SOL HUBEDGES OUT.sol                        put a hub graph (lines "a b", a < KB, b < KA) into a .sol
  build HEXBIN SOL OUT.edges [SOURCES.txt]           re-check every hypothesis, write the edge list, and optionally the
                                                     BFS sources: all hubs and both vertices of every paired element
SETSPEC: optional line "T HHDHDHD" (level types; default HHDHHDD), lines "j k FILE" (FILE: ids of the freed points (H source level) or lines (H^D source level), relative to the
SETSPEC's folder); friendly transitions not listed free nothing."""
import sys, os, hashlib
import numpy as np

T0 = 'HDHDH'; L = RM = Delta = DH = None                 # set by configure() from the type word and q


def configure(T, q):
    global L, RM, Delta, DH
    L = len(T); assert L % 2 == 1 and set(T) <= set('HD')
    RM = (L - 1) // 2; Delta = q + 1 + RM; DH = Delta - L


def load_hex(hexfn):
    b = open(hexfn, 'rb').read()
    q, N, Lc = (int(x) for x in np.frombuffer(b[:12], dtype=np.int32)); Q1 = q + 1
    LP = np.frombuffer(b[12:12 + 4 * Lc * Q1], dtype=np.int32).reshape(Lc, Q1).astype(np.int64)
    flat_p = LP.reshape(-1); flat_l = np.repeat(np.arange(Lc), Q1)
    order = np.lexsort((flat_l, flat_p)); PL = flat_l[order].reshape(N, Q1)
    return q, N, LP, PL, flat_p, flat_l


def load_mirror(mirfn, N):
    mt = open(mirfn).read().split('\n')
    assert mt[0].split()[0] == 'multi' and mt[1].split()[0] == 'freed'
    Rp = np.array([int(v) for v in mt[1].split()[1:]], dtype=np.int64)
    sig = np.array([int(v) for line in mt[3:] for v in line.split()], dtype=np.int64)
    assert len(sig) == N and len(np.unique(sig)) == N
    return Rp, sig


class Model:
    def __init__(self, hexfn, mirfn, sets, T=T0):
        self.T = T; TY = [1 if c == 'D' else 0 for c in T]
        self.q, self.N, self.LP, self.PL, self.fp, self.fl = load_hex(hexfn)
        configure(T, self.q)
        self.Rp, self.sig = load_mirror(mirfn, self.N)
        N = self.N
        self.sinv = np.empty(N, np.int64); self.sinv[self.sig] = np.arange(N)
        self.sets = {key: np.unique(np.asarray(v, np.int64)) for key, v in sets.items()}
        x = np.arange(N)
        self.trs = []
        for j in range(L):
            for k in range(1, RM + 1):
                j2 = (j + k) % L; a, bk = TY[j], 1 - TY[j2]
                if a == bk:
                    img = x; fr = self.sets.get((j, k), np.zeros(0, np.int64))
                else:
                    assert (j, k) not in self.sets, f'set given for non-friendly transition {j}->{j2}'
                    img, fr = (self.sig, np.sort(self.Rp)) if a == 0 else (self.sinv, np.sort(self.sig[self.Rp]))
                self.trs.append(dict(j=j, k=k, j2=j2, a=a, bk=bk, img=img, fr=fr, friendly=(a == bk)))
        # slot lists: per level, arrays of (vertex id, transition index, element)
        A = [[] for _ in range(L)]; B = [[] for _ in range(L)]
        for ti, t in enumerate(self.trs):
            fr = t['fr']
            A[t['j']].append(np.stack([self.vid(t['j'], t['a'], fr), np.full(len(fr), ti), fr], 1))
            B[t['j2']].append(np.stack([self.vid(t['j2'], t['bk'], t['img'][fr]), np.full(len(fr), ti), fr], 1))
        self.A = [np.concatenate(s) if s else np.zeros((0, 3), np.int64) for s in A]
        self.B = [np.concatenate(s) if s else np.zeros((0, 3), np.int64) for s in B]
        self.KB = min(len(s) for s in self.A); self.KA = min(len(s) for s in self.B)
        # (transition, element) -> slot index at its level
        self.aidx = {}; self.bidx = {}
        for lv in range(L):
            for i, (v, ti, e) in enumerate(self.A[lv].tolist()): self.aidx[(ti, e)] = i
            for i, (v, ti, e) in enumerate(self.B[lv].tolist()): self.bidx[(ti, e)] = i
        # vertex id -> slot indices at its level
        self.avert = [{} for _ in range(L)]; self.bvert = [{} for _ in range(L)]
        for lv in range(L):
            for i, v in enumerate(self.A[lv][:, 0].tolist()): self.avert[lv].setdefault(v, []).append(i)
            for i, v in enumerate(self.B[lv][:, 0].tolist()): self.bvert[lv].setdefault(v, []).append(i)

    def vid(self, j, kind, x): return j * 2 * self.N + kind * self.N + np.asarray(x)

    def incident(self, kind, x):
        """elements of the other kind incident with element x of the given kind (lines through a point / points on a line)"""
        return (self.PL if kind == 0 else self.LP)[x]

    def pairs(self, kind, ids):
        """pairs inside ids sharing an incident element; asserts (R1) (at most one partner each)."""
        N = self.N; s = np.zeros(N, bool); s[ids] = True
        inc = self.LP if kind == 0 else self.PL          # other-kind element -> its 12 elements of this kind
        cnt = s[inc].sum(1)
        assert cnt.max() <= 2, '(R1) fails: three freed elements on one line / through one point'
        prs = []
        for c in np.nonzero(cnt == 2)[0]:
            m = inc[c][s[inc[c]]]; prs.append((int(m[0]), int(m[1])))
        deg = np.zeros(N, np.int64)
        for a, b in prs: deg[a] += 1; deg[b] += 1
        assert deg.max() <= 1, '(R1) fails: an element with two partners'
        return prs

    def check_mirror(self):
        N, LP, PL, Rp, sig = self.N, self.LP, self.PL, self.Rp, self.sig
        inRp = np.zeros(N, bool); inRp[Rp] = True; inSR = np.zeros(N, bool); inSR[sig[Rp]] = True
        assert (inRp[LP].sum(1) <= 1).all(), "R' collinear"
        assert (inSR[PL].sum(1) <= 1).all(), "sigma(R') concurrent"
        for x in Rp:
            G2x = np.setdiff1d(LP[PL[x]].reshape(-1), [x]); l = sig[x]
            G2l = np.setdiff1d(PL[LP[l]].reshape(-1), [l])
            assert np.array_equal(np.sort(sig[G2x]), G2l), ('local duality fails at', x)

    def demands(self):
        """the (R2) conditions. colour 0 (point-side hubs, B-slots): fixed B-slot (t, r) at level j2, option: a B-slot at
        level j on an element incident with the partner x. colour 1 (line-side, A-slots): fixed A-slot (t, r) at level
        j, option: an A-slot at level j2 on an element incident with x."""
        dem = {0: [], 1: []}
        for ti, t in enumerate(self.trs):
            if not t['friendly'] or len(t['fr']) == 0: continue
            a, j, j2 = t['a'], t['j'], t['j2']
            prs = self.pairs(a, t['fr'])
            t['pairs'] = prs
            for (r1, r2) in prs:
                for r, x in ((r1, r2), (r2, r1)):
                    inc = self.incident(a, x).tolist()
                    optB = [i for e in inc for i in self.bvert[j].get(int(self.vid(j, 1 - a, e)), [])]
                    dem[0].append(dict(fl=j2, fs=self.bidx[(ti, r)], ol=j, opt=optB, tag=(j, j2, r, x)))
                    optA = [i for e in inc for i in self.avert[j2].get(int(self.vid(j2, 1 - a, e)), [])]
                    dem[1].append(dict(fl=j, fs=self.aidx[(ti, r)], ol=j2, opt=optA, tag=(j, j2, r, x)))
        return dem


def bip_match(nd, opts, forbidden, rng):
    """maximum matching demands 0..nd-1 -> slots (opts[d] list), slots in `forbidden` unusable. Augmenting paths."""
    owner = {}; got = {}
    order = list(range(nd)); rng.shuffle(order)
    sys.setrecursionlimit(100000)
    def aug(d, seen):
        for s in opts[d]:
            if s in forbidden or s in seen: continue
            seen.add(s)
            if s not in owner or aug(owner[s], seen):
                owner[s] = d; got[d] = s; return True
        return False
    for d in order:
        if opts[d]: aug(d, set())
    return got


def do_assign(M, seed):
    """hub slots for both colours. Per option level a maximum matching of the demands to option slots; a demand may take
    the FIXED slot of another demand (its hub then serves both: the levels never clash, e.g. {0, 2} with {2, 3})."""
    rng = np.random.default_rng(seed)
    print('free A-slots per level', [len(s) for s in M.A], 'B-slots', [len(s) for s in M.B], '-> hubs', M.KB, M.KA, flush=True)
    dem = M.demands()
    for ti, t in enumerate(M.trs):
        if t.get('pairs'): print(f"  transition {t['j']}->{t['j2']}: {len(t['fr'])} freed, {len(t['pairs'])} pairs")
    tables = {}; bad = set()
    for c, K, S in ((1, M.KB, M.A), (0, M.KA, M.B)):
        D = dem[c]
        fixown = {}
        for i, d in enumerate(D): fixown[(d['fl'], d['fs'])] = i
        got = {}
        for lv in range(L):
            ids = [i for i, d in enumerate(D) if d['ol'] == lv]
            if not ids: continue
            g = bip_match(len(ids), [D[i]['opt'] for i in ids], set(), rng)
            for loc, s_ in g.items(): got[ids[loc]] = s_
        # union demands that share a fixed slot
        par = list(range(len(D)))
        def find(a):
            while par[a] != a: par[a] = par[par[a]]; a = par[a]
            return a
        for i, s_ in got.items():
            o = fixown.get((D[i]['ol'], s_))
            if o is not None: par[find(i)] = find(o)
        comp = {}
        for i, d in enumerate(D):
            r = find(i); comp.setdefault(r, []).append(i)
        miss = []; hubs = []
        for r, mem in comp.items():
            if any(i not in got for i in mem):
                for i in mem:
                    if i not in got: miss.append(D[i]['tag'])
                # members whose own demand failed: the whole component is dropped from the hub table
                continue
            lvl = {}
            ok = True
            for i in mem:
                for lv_, s_ in ((D[i]['fl'], D[i]['fs']), (D[i]['ol'], got[i])):
                    if lvl.get(lv_, s_) != s_: ok = False
                    lvl[lv_] = s_
            assert ok, 'merged hub with two slots at one level'
            hubs.append(lvl)
        nmerged = sum(1 for m in comp.values() if len(m) > 1)
        # pack constrained hubs whose level sets are disjoint into one hub (first fit by level mask)
        bymask = {}; packed = []
        for lvl in sorted(hubs, key=lambda d: -len(d)):
            m = sum(1 << lv_ for lv_ in lvl)
            tgt = None
            for hm in list(bymask):
                if hm & m == 0 and bymask[hm]: tgt = hm; break
            if tgt is None:
                packed.append(dict(lvl)); bymask.setdefault(m, []).append(len(packed) - 1)
            else:
                h = bymask[tgt].pop(); packed[h].update(lvl); bymask.setdefault(tgt | m, []).append(h)
        print(f'colour {c}: {len(D)} demands, {len(got)} matched, {len(miss)} not served, {len(hubs)} constrained hub '
              f'groups ({nmerged} share a fixed slot), packed into {len(packed)} hubs', flush=True)
        hubs = packed
        for (j, j2, r, x) in miss: bad.add((j, j2, min(r, x), max(r, x)))
        assert len(hubs) <= K, 'more constrained hubs than hubs'
        tab = -np.ones((K, L), np.int64); used = [set() for _ in range(L)]
        for h, lvl in enumerate(hubs):
            for lv_, s_ in lvl.items():
                assert s_ not in used[lv_]
                tab[h, lv_] = s_; used[lv_].add(s_)
        for lv in range(L):
            free = [i for i in range(len(S[lv])) if i not in used[lv]]
            free = list(np.array(free)[rng.permutation(len(free))]) if free else []
            need = np.nonzero(tab[:, lv] < 0)[0]
            assert len(free) >= len(need)
            tab[need, lv] = free[:len(need)]
        tables[c] = tab
    return tables, sorted(bad)


def write_sol(fn, M, tables, hubE, setspec_src):
    with open(fn, 'w') as f:
        f.write(f'typedmirrorL {M.q} {M.N} {M.T} {2 * L * M.N + M.KB + M.KA}\n')
        f.write(f'mirror {setspec_src["mirror"][0]} {setspec_src["mirror"][1]}\n')
        keys = sorted(M.sets)
        f.write(f'sets {len(keys)}\n')
        for (j, k) in keys:
            ids = M.sets[(j, k)]
            f.write(f'set {j} {k} {len(ids)}\n' + ' '.join(map(str, ids.tolist())) + '\n')
        f.write(f'hubs {M.KB} {M.KA}\n')
        for c in (1, 0):
            f.write('\n'.join(' '.join(map(str, r)) for r in tables[c].tolist()) + '\n')
        if hubE is None: f.write('hubgraph 0\n')
        else: f.write(f'hubgraph {len(hubE)}\n' + '\n'.join(f'{a} {b}' for a, b in hubE.tolist()) + '\n')


def read_sol(fn):
    d = os.path.dirname(os.path.abspath(fn))
    lines = open(fn).read().split('\n'); i = 0
    h = lines[i].split(); i += 1; assert h[0] in ('typedmirror3', 'typedmirrorL')
    m = lines[i].split(); i += 1; mirfn = os.path.join(d, m[1])
    assert hashlib.sha256(open(mirfn, 'rb').read()).hexdigest() == m[2], 'mirror sol sha256 mismatch'
    ns = int(lines[i].split()[1]); i += 1
    sets = {}
    for _ in range(ns):
        t = lines[i].split(); i += 1
        ids = np.array([int(v) for v in lines[i].split()], dtype=np.int64); i += 1
        assert t[0] == 'set' and len(ids) == int(t[3]); sets[(int(t[1]), int(t[2]))] = ids
    t = lines[i].split(); i += 1; KB, KA = int(t[1]), int(t[2])
    tA = np.array([[int(v) for v in lines[i + r].split()] for r in range(KB)], dtype=np.int64); i += KB
    tB = np.array([[int(v) for v in lines[i + r].split()] for r in range(KA)], dtype=np.int64); i += KA
    t = lines[i].split(); i += 1; ne = int(t[1])
    he = np.array([[int(v) for v in lines[i + r].split()] for r in range(ne)], dtype=np.int64).reshape(-1, 2)
    return dict(T=h[3], n=int(h[4]), mirfn=mirfn, mirname=m[1], mirsha=m[2], sets=sets, KB=KB, KA=KA, tabs={1: tA, 0: tB}, he=he)


def build(M, S, outfn, srcfn=None):
    N = M.N
    M.check_mirror()
    print(f"mirror hypotheses OK: |R'| = {len(M.Rp)}", flush=True)
    assert (M.KB, M.KA) == (S['KB'], S['KA']), ('hub counts', M.KB, M.KA, S['KB'], S['KA'])
    tabs = S['tabs']
    for c, S_ in ((1, M.A), (0, M.B)):
        tab = tabs[c]
        for lv in range(L):
            col = tab[:, lv]
            assert col.min() >= 0 and col.max() < len(S_[lv]) and len(np.unique(col)) == len(col), ('hub slots', c, lv)
    # (R1) and (R2) for every friendly set
    hubA = {}; hubB = {}
    for lv in range(L):
        for h, i in enumerate(tabs[1][:, lv].tolist()): hubA[(lv, i)] = h
        for h, i in enumerate(tabs[0][:, lv].tolist()): hubB[(lv, i)] = h
    npairs = 0; srcs = []
    for ti, t in enumerate(M.trs):
        if not t['friendly'] or len(t['fr']) == 0: continue
        a, j, j2 = t['a'], t['j'], t['j2']
        prs = M.pairs(a, t['fr'])
        for (r1, r2) in prs:
            for r, x in ((r1, r2), (r2, r1)):
                inc = set(M.vid(j, 1 - a, M.incident(a, x)).tolist())
                h = hubB.get((j2, M.bidx[(ti, r)]))
                assert h is not None, ('(R2a) no point-side hub at', j, j2, r)
                assert int(M.B[j][tabs[0][h, j], 0]) in inc, ('(R2a) fails', j, j2, r, x)
                inc2 = set(M.vid(j2, 1 - a, M.incident(a, x)).tolist())
                h = hubA.get((j, M.aidx[(ti, r)]))
                assert h is not None, ('(R2b) no line-side hub at', j, j2, r)
                assert int(M.A[j2][tabs[1][h, j2], 0]) in inc2, ('(R2b) fails', j, j2, r, x)
                srcs += [int(M.vid(j, a, r)), int(M.vid(j2, t["bk"], r))]
        npairs += len(prs)
        print(f"  {j}->{j2} ({'points' if a == 0 else 'lines'}): {len(t['fr'])} freed, {len(prs)} pairs, (R1) and (R2) OK", flush=True)
    print(f'friendly hypotheses OK ({npairs} pairs in all)', flush=True)
    VID = lambda j, kind, x: j * 2 * N + kind * N + x
    out = [np.stack([VID(j, 0, M.fp), VID(j, 1, M.fl)], axis=1) for j in range(L)]
    x = np.arange(N)
    for t in M.trs:
        keep = np.ones(N, bool); keep[t['fr']] = False
        out.append(np.stack([VID(t['j'], t['a'], x[keep]), VID(t['j2'], t['bk'], t['img'][keep])], axis=1))
    NV0 = 2 * N * L; KB, KA = M.KB, M.KA; n = NV0 + KB + KA
    for lv in range(L):
        out.append(np.stack([NV0 + np.arange(KB), M.A[lv][tabs[1][:, lv], 0]], axis=1))
        out.append(np.stack([NV0 + KB + np.arange(KA), M.B[lv][tabs[0][:, lv], 0]], axis=1))
    he = S['he']
    if len(he):
        assert (he[:, 0] >= 0).all() and (he[:, 0] < KB).all() and (he[:, 1] >= 0).all() and (he[:, 1] < KA).all()
        assert len(np.unique(he, axis=0)) == len(he)
        out.append(np.stack([NV0 + he[:, 0], NV0 + KB + he[:, 1]], axis=1))
    E = np.concatenate(out)
    deg = np.bincount(E.reshape(-1), minlength=n)
    key = np.minimum(E[:, 0], E[:, 1]) * n + np.maximum(E[:, 0], E[:, 1])
    assert len(np.unique(key)) == len(E), 'repeated edge'
    print(f'n = {n}, edges = {len(E)}, degree min {deg.min()} max {deg.max()}, hub graph edges {len(he)}', flush=True)
    assert deg.max() <= Delta and n == S['n']
    with open(outfn, 'w') as f:
        f.write('%d\n' % n)
        CH = 1 << 21
        for i in range(0, len(E), CH):
            f.write('\n'.join('%d %d' % (u, v) for u, v in E[i:i + CH].tolist())); f.write('\n')
    print('wrote', outfn, flush=True)
    if srcfn:
        allsrc = np.unique(np.concatenate([np.arange(NV0, n), np.array(srcs, np.int64)]))
        np.savetxt(srcfn, allsrc, fmt='%d'); print(f'wrote {srcfn}: {len(allsrc)} BFS sources (hubs and paired elements)')


def read_setspec(fn):
    """lines 'j k FILE'; an optional line 'T <7-letter pattern>' sets the level types (default HHDHHDD)."""
    sets = {}; d = os.path.dirname(os.path.abspath(fn)); T = T0
    for line in open(fn):
        t = line.split()
        if not t or t[0].startswith('#'): continue
        if t[0] == 'T': T = t[1]; continue
        sets[(int(t[0]), int(t[1]))] = np.loadtxt(os.path.join(d, t[2]), dtype=np.int64).reshape(-1)
    return sets, T


def main():
    mode = sys.argv[1]
    if mode == 'assign':
        hexfn, mirfn, spec, seed, outsol = sys.argv[2:7]
        sets, T = read_setspec(spec)
        M = Model(hexfn, mirfn, sets, T)
        tables, bad = do_assign(M, int(seed))
        if bad:
            with open(outsol + '.unserved', 'w') as f:
                for b in bad: f.write(' '.join(map(str, b)) + '\n')
            print(f'{len(bad)} pairs not served: listed in {outsol}.unserved (j j2 r x); drop one end of each and rerun')
            return 3
        src = {'mirror': (os.path.basename(mirfn), hashlib.sha256(open(mirfn, 'rb').read()).hexdigest())}
        write_sol(outsol, M, tables, None, src); print('wrote', outsol)
    elif mode == 'sethub':
        solfn, hef, outsol = sys.argv[2:5]
        txt = open(solfn).read().split('\n')
        k = [i for i, l in enumerate(txt) if l.startswith('hubgraph')][0]
        he = np.loadtxt(hef, dtype=np.int64).reshape(-1, 2)
        with open(outsol, 'w') as f:
            f.write('\n'.join(txt[:k]) + '\n' + f'hubgraph {len(he)}\n' + '\n'.join(f'{a} {b}' for a, b in he.tolist()) + '\n')
        print('wrote', outsol)
    elif mode == 'build':
        hexfn, solfn, outfn = sys.argv[2:5]; srcfn = sys.argv[5] if len(sys.argv) > 5 else None
        S = read_sol(solfn)
        M = Model(hexfn, S['mirfn'], S['sets'], S['T'])
        print('free A-slots per level', [len(s) for s in M.A], 'B-slots', [len(s) for s in M.B], '-> hubs', M.KB, M.KA, flush=True)
        build(M, S, outfn, srcfn)
    return 0


if __name__ == '__main__':
    sys.exit(main())
