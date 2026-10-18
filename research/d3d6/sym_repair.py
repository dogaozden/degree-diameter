"""Like sym_search.py, but only the degree (triple) conditions are hard; frames are ranked by the number of
R_g-on-L_h incidences and the best are built and checked.  python3 sym_search2.py q ntest"""
import itertools, json, sys
from singer import singer_plane
from multi_gadget import lib, HERE, gadget_incidences
from repair import repair

q = int(sys.argv[1]); ntest = int(sys.argv[2])
points, lines = singer_plane(q); n = len(points); s3 = n // 3
LT = {}
for j, L in enumerate(lines):
    for a, b in itertools.combinations(sorted(L), 2): LT[a, b] = j
lt = lambda a, b: LT[min(a, b), max(a, b)]
MP = {}
for p in points:
    th = [j for j, L in enumerate(lines) if p in L]
    for a, b in itertools.combinations(th, 2): MP[a, b] = p
mp = lambda a, b: MP[min(a, b), max(a, b)]
def sh(fr, t):
    A, ell, P, X = fr
    return ((A + t) % n, (ell + t) % n, (P + t) % n, [(x + t) % n for x in X])
def sets(fr):
    A, ell, P, X = fr
    return [A] + list(X), [ell] + [lt(A, x) for x in X]
def score(frames):
    S = [sets(f) for f in frames]
    for a in S[0][0]:
        for b in S[1][0]:
            if a == b: return None
            L = lines[lt(a, b)]
            if any(x in L for x in S[2][0]): return None
    for a in S[0][1]:
        for b in S[1][1]:
            if a == b: return None
            p = mp(a, b)
            if any(p in lines[x] for x in S[2][1]): return None
    return sum(1 for g1, g2 in itertools.permutations(range(3), 2) for x in S[g1][0] for L in S[g2][1] if x in lines[L])
cands = []
for ell in range(n):
    if 0 in lines[ell]: continue
    for X in itertools.combinations(sorted(lines[ell]), 4):
        fr = (0, ell, 0, list(X)); s = score([fr, sh(fr, s3), sh(fr, 2 * s3)])
        if s is not None: cands.append((s, ell, X))
cands.sort()
print('degree-feasible frames:', len(cands), 'pair-incidence histogram:',
      {k: sum(1 for c in cands if c[0] == k) for k in sorted({c[0] for c in cands})[:8]}, flush=True)
for s, ell, X in cands[:ntest]:
    for P in sorted(lines[ell]):
        if P in X: continue
        fr = (0, ell, P, list(X)); frames = [fr, sh(fr, s3), sh(fr, 2 * s3)]
        inc = gadget_incidences(lines, frames)
        pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
        ids = {v: i for i, v in enumerate(pts + lns)}; N = len(ids)
        E = sorted((ids[a], ids[b]) for a, b in inc); side = [0] * len(pts) + [1] * len(lns)
        md = lib.max_degree(N, E)
        E2 = repair(N, E, side, q + 3, 3, verbose=True) if md <= q + 3 else None
        ok = E2 is not None and lib.is_valid(N, E2, q + 3, 3)
        if ok: E = E2
        print(f'pairs={s} ell={ell} X={X} P={P}: n={N} maxdeg={md} valid={ok}', flush=True)
        if ok:
            out = HERE / 'graphs' / f'sym3_q{q}_d{q+3}_n{N}.json'
            out.write_text(json.dumps({'case': f'd{q+3}D3', 'value': N, 'output': [N, E]}))
            json.dump(frames, open(HERE / 'runs' / f'sym3_q{q}_frames.json', 'w')); print('wrote', out); sys.exit(0)
        break
