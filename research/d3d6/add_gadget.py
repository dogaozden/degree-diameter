"""Add one more +2 gadget to existing frames in the Singer plane, at Delta = q+3, then repair.
python3 add_gadget.py q frames.json ntest out_tag"""
import itertools, json, sys
from singer import singer_plane
from multi_gadget import lib, HERE, gadget_incidences
from repair import repair

q = int(sys.argv[1]); frames = [tuple(f) for f in json.load(open(sys.argv[2]))]
ntest = int(sys.argv[3]); tag = sys.argv[4]
points, lines = singer_plane(q); n = len(points); Delta = q + 3


def build(frs):
    inc = gadget_incidences(lines, frs)
    pts = sorted({a for a, b in inc}, key=str); lns = sorted({b for a, b in inc}, key=str)
    ids = {v: i for i, v in enumerate(pts + lns)}
    E = sorted((ids[a], ids[b]) for a, b in inc)
    return len(ids), E, [0] * len(pts) + [1] * len(lns), ids


N0, E0, side0, ids0 = build(frames)
deg = [0] * N0
for u, v in E0: deg[u] += 1; deg[v] += 1
pdeg = {p: deg[ids0[('p', p)]] for p in points}
ldeg = {j: deg[ids0[('l', j)]] for j in range(n)}
okP = {p for p in points if pdeg[p] <= Delta - 1}
okL = {j for j in range(n) if ldeg[j] <= Delta - 1}
thru = [[j for j in range(n) if p in lines[j]] for p in points]
special = {x for f in frames for x in [f[0]] + list(f[3])}
cands = []
for A in points:
    if A in special or not all(j in okL for j in thru[A]): continue
    for ell in range(n):
        if A in lines[ell] or not lines[ell] <= okP: continue
        good = []
        for x in lines[ell]:
            ax = next(j for j in thru[A] if x in lines[j])
            if x not in special and lines[ax] <= okP and all(j in okL for j in thru[x]):
                good.append(x)
        for X in itertools.combinations(sorted(good), 4):
            cands.append((A, ell, X, [x for x in lines[ell] if x not in X]))
print('candidates', len(cands), flush=True)
best = None
for A, ell, X, rest in cands[:ntest]:
    fr = (A, ell, rest[0], list(X))
    N, E, side, _ = build(frames + [fr])
    if lib.max_degree(N, E) > Delta: continue
    E2 = repair(N, E, side, Delta, 3)
    ok = E2 is not None and lib.is_valid(N, E2, Delta, 3)
    print(f'A={A} ell={ell} X={X}: n={N} repaired={E2 is not None} valid={ok}', flush=True)
    if ok:
        out = HERE / 'graphs' / f'{tag}_q{q}_d{Delta}_n{N}.json'
        out.write_text(json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E2]}))
        json.dump(frames + [fr], open(HERE / 'runs' / f'{tag}_q{q}_frames.json', 'w'))
        print('wrote', out, flush=True); break
