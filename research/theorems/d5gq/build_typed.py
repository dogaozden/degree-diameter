"""Typed level graph with surgery and hubs over Q(4,q) (Corollary 8.x of D5_QUADRANGLE.md).

H-levels are Q(4,q) (A = points of Q(4,q) = lines of W(q)); D-levels are its dual W(q) (A = lines of Q(4,q) = points
of W(q)).  Friendly transitions carry the identity: H->D frees an ovoid of Q(4,q) (= a spread of W(q)), D->H frees a
partial spread of Q(4,q) (= a partial ovoid of W(q)).  Non-friendly transitions carry the index bijection
M(p) = line with the same index (points and lines of Q(4,q) are both numbered 0..N-1) and free nothing, unless
`pairs` gives local dualities (not used here).  Hubs: B-hub h takes the h-th free A-slot of every level, A-hub g the
g-th free B-slot; the hub graph Y is random with max degree q - r, retried until (HG) holds.

usage: python3 build_typed.py q r TYPES ARCS_JSON|rot  [partial_ovoid_json]  out_prefix
"""
import sys, json, random, os
import numpy as np
from gqlib import W, Q4, regular_spread_W, is_partial_ovoid, is_partial_spread
from levels import build, write_edges, apsp, rotational_arcs


def greedy_partial_ovoid(G, seed=0, tries=200):
    rng = random.Random(seed); best = []
    for _ in range(tries):
        order = list(range(G.np)); rng.shuffle(order); S = []
        bad = np.zeros(G.np, dtype=bool)
        for p in order:
            if not bad[p]:
                S.append(p); bad |= G.col[p]; bad[p] = True
        if len(S) > len(best): best = S
    return sorted(best)


def hub_distance_ok(n, edges, hubs_B, hubs_A):
    """same-colour hubs within distance 4 (BFS from each hub, depth 4)"""
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b); adj[b].append(a)
    for group in (hubs_B, hubs_A):
        gs = set(group)
        for h in group:
            seen = {h}; fr = [h]
            for _ in range(4):
                nf = []
                for x in fr:
                    for y in adj[x]:
                        if y not in seen: seen.add(y); nf.append(y)
                fr = nf
            if not gs <= seen:
                return False
    return True


def main():
    q, r = int(sys.argv[1]), int(sys.argv[2]); types = sys.argv[3]
    arcs = rotational_arcs(len(types)) if sys.argv[4] == 'rot' else [tuple(a) for a in json.load(open(sys.argv[4]))]
    po_file = sys.argv[5] if len(sys.argv) > 6 else None
    out = sys.argv[-1]
    Wq = W(q); G = Wq.dual('Q(4,%d)' % q)          # G = Q(4,q): points of G = lines of W(q)
    N = G.np; assert G.nl == N
    ovoid = regular_spread_W(Wq)                    # spread of W(q) = ovoid of Q(4,q) (point ids of G)
    assert is_partial_ovoid(G, ovoid) and len(ovoid) == q * q + 1
    if po_file:
        pspread = sorted(json.load(open(po_file)))  # partial ovoid of W(q) = partial spread of G (line ids of G)
    else:
        pspread = greedy_partial_ovoid(Wq)
    assert is_partial_ovoid(Wq, pspread) and is_partial_spread(G, pspread)
    L = len(types)
    M, R = {}, {}
    for (u, v) in arcs:
        M[(u, v)] = list(range(N))                  # identity (friendly) or index bijection (non-friendly)
        if types[u] == 'H' and types[v] == 'D':
            R[(u, v)] = set(ovoid)
        elif types[u] == 'D' and types[v] == 'H':
            R[(u, v)] = set(pspread)
        else:
            R[(u, v)] = set()
            if os.environ.get('LD', '0') == '1':
                # two-point local duality (Proposition 6.4): H->H on G (points -> lines), D->D on W(q) = G^D
                from localdual import local_duality_pair, pick_pair
                Hq = G if types[u] == 'H' else Wq
                avoid_a = ovoid if types[u] == 'H' else pspread
                x, y, l, m = pick_pair(Hq, avoid_pts=avoid_a)
                M[(u, v)] = local_duality_pair(Hq, x, y, l, m)
                R[(u, v)] = {x, y}
    Aslots = {j: [] for j in range(L)}; Bslots = {j: [] for j in range(L)}
    for (u, v) in arcs:
        for a in sorted(R[(u, v)]):
            Aslots[u].append((u, a, (u, v)))
            Bslots[v].append((v, M[(u, v)][a], (u, v)))
    KB = min(len(Aslots[j]) for j in range(L)); KA = min(len(Bslots[j]) for j in range(L))
    alpha = [len(Aslots[j]) for j in range(L)]; beta = [len(Bslots[j]) for j in range(L)]
    print('q=%d r=%d types=%s |ovoid|=%d |pspread|=%d alpha=%s beta=%s K_B=%d K_A=%d' % (q, r, types, len(ovoid), len(pspread), alpha, beta, KB, KA))
    Bhubs = [[Aslots[j][h] for j in range(L)] for h in range(KB)]
    Ahubs = [[Bslots[j][g] for j in range(L)] for g in range(KA)]
    delta = q - r
    from hubopt import hub_D0, search, bad_pairs
    n0, E0 = build(G, types, M, R, Bhubs, Ahubs, [], arcs=arcs)
    nv = L * 2 * N
    hubs = list(range(nv, nv + KB + KA))
    D0 = hub_D0(n0, E0, hubs)
    print('level-only same-colour hub pairs within 4: B %d of %d, A %d of %d' % (
        ((D0[:KB, :KB] <= 4).sum() - KB) // 2, KB * (KB - 1) // 2, ((D0[KB:, KB:] <= 4).sum() - KA) // 2, KA * (KA - 1) // 2))
    for sd in range(int(os.environ.get("HUBSEEDS", "4"))):
        Y, cost = search(D0, KB, KA, delta, seed=sd, iters=int(os.environ.get("HUBITERS", "6000")), verbose=False)
        print("  hub search seed", sd, "bad", cost)
        if cost == 0: break
    if cost:
        print('no hub graph found, bad pairs', cost); return
    attempt = 0
    n, E = build(G, types, M, R, Bhubs, Ahubs, Y, arcs=arcs)
    print('hub graph attempt', attempt, 'edges', len(Y))
    path = out + '.edges'
    write_edges(path, n, E)
    sol = dict(q=q, r=r, types=types, arcs=arcs, ovoid_Q4=ovoid, pspread_Q4=pspread, K_B=KB, K_A=KA, Y=Y,
               note='G = Q(4,q) built as gqlib.W(q).dual(); points of G = lines of W(q); M = identity on indices')
    json.dump(sol, open(out + '.json', 'w'))
    print(apsp(path, q + 1 + r, 5, threads=2))


if __name__ == '__main__':
    main()
