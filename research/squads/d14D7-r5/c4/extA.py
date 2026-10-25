#!/usr/bin/env python3
"""c4: non-abelian extensions of a torus subgroup A (given by exponent vectors) by normaliser elements n = w*t,
w in W0 (block swaps, inversions, Frobenius), t random in T.  G = <A, n> is run through orbclq.
usage: extA.py --A "0,2,0,0;0,0,2,0" --max 8 --t 15 --seed 1 --tag z55"""
import sys, os, json, random, argparse, time, hashlib
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import normext as N

ap = argparse.ArgumentParser()
ap.add_argument('--A', required=True)
ap.add_argument('--max', type=int, default=8)
ap.add_argument('--t', type=float, default=15)
ap.add_argument('--seed', type=int, default=1)
ap.add_argument('--tag', default='ext')
ap.add_argument('--tries', type=int, default=400)
ap.add_argument('--maxG', type=int, default=300)
a = ap.parse_args()

T = N.Torus(['E', 'H', 'H', 'L'])
Aexps = [tuple(int(x) for x in s.split(',')) for s in a.A.split(';')]
Ael = [T.elems[T.index[e]] for e in Aexps]
Akeys = set(N.closure(Ael, limit=2000).keys())
print('|A| =', len(Akeys), flush=True)
rng = random.Random(a.seed)
seen, results = set(), []
for _ in range(a.tries):
    if len(results) >= a.max:
        break
    w = T.Wlist[rng.randrange(1, len(T.Wlist))]
    ti = rng.randrange(len(T.elems))
    n = N.mm(w, T.elems[ti])
    G = N.closure(Ael + [n], limit=a.maxG)
    if G is None or len(G) <= len(Akeys):
        continue
    dig = hashlib.sha1(b''.join(sorted(G.keys()))).hexdigest()[:16]
    if dig in seen:
        continue
    seen.add(dig)
    abelian = all((N.mm(x, y) == N.mm(y, x)).all() for x in Ael + [n] for y in Ael + [n])
    name = f'{a.tag}_w{T.Wnames[N.key(w)]}_t{ti}_o{len(G)}'
    gens_std = [T.to_std(M) for M in Ael + [n]]
    gpath = os.path.join(N.GENS, name + '.txt')
    N.L.write_gens(gpath, [M.tolist() for M in gens_std], f'c4 extA: A={a.A} + normaliser element, |G|={len(G)}')
    outp = os.path.join(N.SETS, name + '.txt')
    t0 = time.time()
    res, rc, err = N.run_orbclq(gpath, outp, a.t, a.seed)
    best = int(res.get('best', 0))
    rec = dict(name=name, types=['E', 'H', 'H', 'L'], A=a.A, weyl=T.Wnames[N.key(w)], tdesc=list(T.exps[ti]),
               order=len(G), abelian=abelian, K=res.get('good'), best=best, exact=res.get('exact'),
               pairs_orthogonal=res.get('pairs_orthogonal'), rc=rc, wall=round(time.time() - t0, 1))
    with open(N.RUNS, 'a') as f:
        f.write(json.dumps(rec) + '\n')
    print(f"{name} |G|={len(G)} abel={int(abelian)} K={res.get('good')} best={best} exact={res.get('exact')} rc={rc}",
          flush=True)
    if best < 740 and os.path.exists(outp):
        os.remove(outp)
    results.append(best)
print('done; bests', results, flush=True)
