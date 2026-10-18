"""3 gadgets related by the order-3 Singer subgroup x -> x + n/3 of PG(2,q) (q prime, 3 | q^2+q+1).
Enumerates frames with A = 0 (translations commute with the subgroup), keeps those meeting the load and
incidence conditions of frame_search.py, then builds and checks the graph at Delta = q+3.
python3 sym_search.py q [max_valid]"""
import itertools, json, sys
from singer import singer_plane
from multi_gadget import lib, HERE, gadget_incidences, to_graph

q = int(sys.argv[1]); maxv = int(sys.argv[2]) if len(sys.argv) > 2 else 1
points, lines = singer_plane(q); n = len(points); s3 = n // 3
D0 = sorted(lines[0])
def lt(a, b):
    # line D + j containing a and b: a - b = d1 - d2
    for d1 in D0:
        j = (a - d1) % n
        if b in lines[j]: return j
idxline = {L: j for j, L in enumerate(lines)}
def sh(fr, t):
    A, ell, P, X = fr
    return ((A + t) % n, (ell + t) % n, (P + t) % n, [(x + t) % n for x in X])
def sets(fr):
    A, ell, P, X = fr
    return [A] + list(X), [ell] + [lt(A, x) for x in X]
def meetpt(a, b):
    s = lines[a] & lines[b]; return next(iter(s))
def cost(frames):
    S = [sets(f) for f in frames]; c = 0
    for g1, g2, g3 in itertools.combinations(range(3), 3):
        for a in S[g1][0]:
            for b in S[g2][0]:
                if a == b: return 99
                L = lines[lt(a, b)]
                if any(x in L for x in S[g3][0]): return 99
        for a in S[g1][1]:
            for b in S[g2][1]:
                if a == b: return 99
                p = meetpt(a, b)
                if any(p in lines[x] for x in S[g3][1]): return 99
    for g1, g2 in itertools.permutations(range(3), 2):
        if any(x in lines[L] for x in S[g1][0] for L in S[g2][1]): return 99
    return 0
A = 0; found = 0; tested = 0
for ell in range(n):
    if A in lines[ell]: continue
    on = sorted(lines[ell])
    for X in itertools.combinations(on, 4):
        # cheap pair check first: R_0 vs L_1 and L_2
        fr = (A, ell, 0, list(X))
        frames = [fr, sh(fr, s3), sh(fr, 2 * s3)]
        tested += 1
        if cost(frames): continue
        for P in on:
            if P in X: continue
            for perm in itertools.permutations(X):
                fr = (A, ell, P, list(perm)); frames = [fr, sh(fr, s3), sh(fr, 2 * s3)]
                N, E = to_graph(gadget_incidences(lines, frames))
                md = lib.max_degree(N, E); ok = md <= q + 3 and lib.is_valid(N, E, q + 3, 3)
                print(f'ell={ell} X={perm} P={P}: n={N} maxdeg={md} valid={ok}', flush=True)
                if ok:
                    out = HERE / 'graphs' / f'sym3_q{q}_d{q+3}_n{N}.json'
                    out.write_text(json.dumps({'case': f'd{q+3}D3', 'value': N, 'output': [N, E]}))
                    json.dump(frames, open(HERE / 'runs' / f'sym3_q{q}_frames.json', 'w'))
                    print('wrote', out); found += 1
                    if found >= maxv: sys.exit(0)
                break
            break
print('tested', tested, 'found', found)
