"""Find k gadget frames in PG(2,q) so that k +2 gadgets fit at Delta = q+3 (every plane vertex loaded <= 2 times),
then build the graph with multi_gadget.py rules and check it.

Load of gadget g: points of ell_g and of the 4 lines A_g X_s (set U_g); lines through A_g or an X_s (dual).
So we need: no three points from R_g = {A_g, X_s} of three different gadgets collinear, and no three lines from
{ell_g, A_g X_s} of three different gadgets concurrent.  (Coincidences count as collinear / concurrent.)
python3 frame_search.py q k restarts [seed]
"""
import itertools
import json
import random
import sys

from multi_gadget import C, lib, HERE, gadget_incidences, to_graph


def main():
    q, k, restarts = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
    seed = int(sys.argv[4]) if len(sys.argv) > 4 else 1
    rng = random.Random(seed)
    points, lines = C.pg_plane(q)
    npt = len(points)
    LT = {}
    for j, L in enumerate(lines):
        for a, b in itertools.combinations(sorted(L), 2):
            LT[a, b] = j
    def lt(a, b):
        return LT[min(a, b), max(a, b)]
    thru = [[j for j, L in enumerate(lines) if p in L] for p in points]
    meet = {}
    for p in points:
        for a, b in itertools.combinations(thru[p], 2):
            meet[a, b] = p
    def mt(a, b):
        return meet[min(a, b), max(a, b)]

    def rand_frame():
        ell = rng.randrange(npt)
        A = rng.choice([p for p in points if p not in lines[ell]])
        X = rng.sample(sorted(lines[ell]), 5)
        return [A, ell, X[0], X[1:]]

    def sets(fr):
        A, ell, P, X = fr
        R = [A] + list(X)
        Ls = [ell] + [lt(A, x) for x in X]
        return R, Ls

    def cost(frames):
        S = [sets(f) for f in frames]
        c = 0
        for g1, g2, g3 in itertools.combinations(range(k), 3):
            for a in S[g1][0]:
                for b in S[g2][0]:
                    if a == b:
                        c += len(S[g3][0]); continue
                    L = lines[lt(a, b)]
                    c += sum(1 for x in S[g3][0] if x in L)
            for a in S[g1][1]:
                for b in S[g2][1]:
                    if a == b:
                        c += len(S[g3][1]); continue
                    p = mt(a, b)
                    c += sum(1 for x in S[g3][1] if p in lines[x])
        # pairwise distinctness of special elements
        for g1, g2 in itertools.combinations(range(k), 2):
            c += len(set(S[g1][0]) & set(S[g2][0])) + len(set(S[g1][1]) & set(S[g2][1]))
            c += (frames[g1][1] == frames[g2][1]) + (frames[g1][0] == frames[g2][0])
            for ga, gb in ((g1, g2), (g2, g1)):
                c += sum(1 for x in S[ga][0] for L in S[gb][1] if x in lines[L])
        return c

    def mutate(fr):
        A, ell, P, X = fr
        r = rng.random()
        if r < 0.5:
            others = [p for p in lines[ell] if p != P and p not in X]
            i = rng.randrange(4); X = list(X); X[i] = rng.choice(others)
            return [A, ell, P, X]
        if r < 0.9:
            return [rng.choice([p for p in points if p not in lines[ell]]), ell, P, X]
        return rand_frame()

    for rs in range(restarts):
        frames = [rand_frame() for _ in range(k)]
        c = cost(frames)
        import math
        iters = int(sys.argv[5]) if len(sys.argv) > 5 else 100000
        for it in range(iters):
            if c == 0:
                break
            T = 2.0 * (1 - it / iters) + 0.2
            g = rng.randrange(k); new = list(frames); new[g] = mutate(frames[g])
            c2 = cost(new)
            if c2 <= c or rng.random() < math.exp((c - c2) / T):
                frames, c = new, c2
        if c:
            print(f'restart {rs}: stuck at cost {c}', flush=True)
            continue
        fr = [(f[0], f[1], f[2], f[3]) for f in frames]
        n, edges = to_graph(gadget_incidences(lines, fr))
        md = lib.max_degree(n, edges)
        ok = md <= q + 3 and lib.is_valid(n, edges, q + 3, 3)
        print(f'restart {rs}: cost 0, n={n}, maxdeg={md}, valid={ok}', flush=True)
        json.dump(fr, open(HERE / 'runs' / f'cost0_q{q}_k{k}_s{seed}_r{rs}.json', 'w'))
        if ok:
            out = HERE / 'graphs' / f'multi_q{q}_k{k}_d{q+3}_n{n}.json'
            out.write_text(json.dumps({'case': f'd{q+3}D3', 'value': n, 'output': [n, edges]}))
            json.dump(fr, open(HERE / 'runs' / f'multi_q{q}_k{k}_frames.json', 'w'))
            print('  wrote', out, flush=True)
            return


if __name__ == '__main__':
    main()
