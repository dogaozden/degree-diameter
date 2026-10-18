"""Local search for the duplication problem (see dup_ilp.py): max sum m(u), m(u) in {0..maxmult},
deg(w) + sum_{u~w} m(u) <= Delta.  python3 dup_ls.py base q Delta [seconds] [maxmult]"""
import json, math, random, sys, time
from dup_ilp import base_graph, twin, HERE, lib


def ls_side(adj, deg, side, which, Delta, secs, maxmult, rng):
    var = [u for u in range(len(adj)) if side[u] == which and deg[u] <= Delta]
    slack = [Delta - deg[w] for w in range(len(adj))]
    m = {u: 0 for u in var}
    load = [0] * len(adj)
    def viol_delta(u, d):
        s = 0
        for w in adj[u]:
            before = max(0, load[w] - slack[w]); after = max(0, load[w] + d - slack[w]); s += after - before
        return s
    size = 0; viol = 0; best = (0, dict(m)); t0 = time.time(); T = 1.0; it = 0
    while time.time() - t0 < secs:
        it += 1
        if it % 2000 == 0:
            T = max(0.05, 1.0 * (1 - (time.time() - t0) / secs))
        u = rng.choice(var); d = rng.choice((-1, 1))
        if not 0 <= m[u] + d <= maxmult:
            continue
        dv = viol_delta(u, d); de = d - 2.0 * dv
        if de >= 0 or rng.random() < math.exp(de / T):
            m[u] += d; size += d; viol += dv
            for w in adj[u]:
                load[w] += d
            if viol == 0 and size > best[0]:
                best = (size, {k: v for k, v in m.items() if v})
    return best


def main():
    base, q, Delta = sys.argv[1], int(sys.argv[2]), int(sys.argv[3])
    secs = float(sys.argv[4]) if len(sys.argv) > 4 else 30
    maxmult = int(sys.argv[5]) if len(sys.argv) > 5 else 2
    n, edges, side = base_graph(base, q)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v); adj[v].append(u)
    deg = [len(a) for a in adj]
    rng = random.Random(1)
    mult = {}
    for which in (0, 1):
        s, m = ls_side(adj, deg, side, which, Delta, secs, maxmult, rng)
        print(f'{base} q={q} D={Delta} side {which}: {s}', flush=True)
        mult.update(m)
    N, E = twin(n, edges, mult)
    ok = lib.is_valid(N, E, Delta, 3)
    print(f'  n={n} -> {N} valid={ok}')
    if ok:
        (HERE / 'graphs' / f'dupls_{base}_q{q}_d{Delta}_n{N}.json').write_text(
            json.dumps({'case': f'd{Delta}D3', 'value': N, 'output': [N, E]}))


if __name__ == '__main__':
    main()
