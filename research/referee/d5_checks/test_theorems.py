"""Two-level tests of Theorem E, Theorem B, Theorem C / Prop. 6.4, Prop. 7.1 and Prop. 7.2 against a BFS in the
two-level graph (level edges of both levels and the remaining matching edges of t, any number of them)."""
import random, itertools, sys
from collections import deque
from gf import GF
from gq import W, Q4
from families import local_duality

def two_level_bad(G, typ0, typ1, M, R, extra=()):
    """levels 0 (type typ0) -> 1 (type typ1); returns set of (u,v) pairs (u in level 0, v in level 1) at
    distance > 5 in the two-level graph (plus optional extra vertices, given as lists of neighbours)."""
    N = G.N
    A = {'H': 'P', 'D': 'L'}; B = {'H': 'L', 'D': 'P'}
    vid = lambda j, t, e: j * 2 * N + (e if t == 'P' else N + e)
    nv = 4 * N + len(extra)
    adj = [[] for _ in range(nv)]
    def add(u, v):
        adj[u].append(v); adj[v].append(u)
    for j in (0, 1):
        for l in range(N):
            for p in G.lp[l]:
                add(vid(j, 'P', p), vid(j, 'L', l))
    Rs = set(R)
    for a in range(N):
        if a not in Rs:
            add(vid(0, A[typ0], a), vid(1, B[typ1], M[a]))
    for i, nb in enumerate(extra):
        for (j, t, e) in nb:
            add(4 * N + i, vid(j, t, e))
    bad = set()
    for s in range(2 * N):
        dist = [-1] * nv; dist[s] = 0; dq = deque([s])
        while dq:
            x = dq.popleft()
            if dist[x] == 5:
                continue
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1; dq.append(y)
        for v in range(2 * N, 4 * N):
            if dist[v] < 0:
                bad.add((s, v - 2 * N))
    return bad

def gamma2(G, t):
    return G.collinear if t == 'P' else G.meets
def incident(G, t):   # elements incident with an element of type t
    return G.pl if t == 'P' else G.lp

def E2E3(G, typ0, typ1, M, R):
    A = {'H': 'P', 'D': 'L'}; B = {'H': 'L', 'D': 'P'}
    tA0, tB0, tA1, tB1 = A[typ0], B[typ0], A[typ1], B[typ1]
    Rs = set(R); N = G.N
    G2A0 = gamma2(G, tA0); G2B1 = gamma2(G, tB1)
    incA1 = incident(G, tA1)       # elements (type tB1) incident with an element of A(tau_1)
    incB0 = incident(G, tB0)       # elements (type tA0) incident with an element of B(tau_0)
    e2 = e3 = True
    for x in R:
        imgs = {M[a] for a in G2A0[x] if a not in Rs}
        if not all(any(y in imgs for y in incA1[v]) for v in range(N)):
            e2 = False
        good = {a for a in range(N) if a not in Rs and M[a] in G2B1[M[x]]}
        if not all(any(a in good for a in incB0[u]) for u in range(N)):
            e3 = False
    return e2, e3

def main():
    rng = random.Random(int(sys.argv[1]) if len(sys.argv) > 1 else 0)
    counts = {}
    def tally(key):
        counts[key] = counts.get(key, 0) + 1
    for q in (2, 3, 4, 5):
        F = GF(q); Wq = W(F); Qq = Q4(F)
        for G, name in ((Wq, 'W'), (Qq, 'Q')):
            N = G.N
            for trial in range(40):
                typ0, typ1 = rng.choice([('H', 'D'), ('D', 'H'), ('H', 'H'), ('D', 'D')])
                friendly = typ0 != typ1
                A = {'H': 'P', 'D': 'L'}
                kind = rng.choice(['random', 'random', 'ovoid', 'pencil', 'localdual'])
                if kind == 'localdual' and not friendly:
                    M, R = local_duality(G, A[typ0], rng)
                else:
                    M = list(range(N)) if (friendly and rng.random() < 0.6) else rng.sample(range(N), N)
                    if kind == 'ovoid':      # greedy random partial ovoid / spread of type A(tau_0)
                        g2 = gamma2(G, A[typ0]); R = []
                        for x in rng.sample(range(N), N):
                            if all(x not in g2[y] for y in R):
                                R.append(x)
                        R = R[:rng.randint(1, len(R))]
                    elif kind == 'pencil':   # all elements incident with one element, plus random ones
                        inc = incident(G, 'L' if A[typ0] == 'P' else 'P')
                        R = list(inc[rng.randrange(N)]) + rng.sample(range(N), rng.randint(0, 2))
                        R = sorted(set(R))
                    else:
                        R = rng.sample(range(N), rng.randint(1, 4))
                bad = two_level_bad(G, typ0, typ1, M, R)
                e2, e3 = E2E3(G, typ0, typ1, M, R)
                assert (not bad) == (e2 and e3), (q, name, typ0, typ1, kind)
                tally(('E agrees', 'repaired' if not bad else 'E2 fails only' if (not e2 and e3) else
                       'E3 fails only' if (e2 and not e3) else 'both fail'))
                # Theorem B: friendly with M = id (automorphic): repaired iff R non-collinear / non-concurrent
                if friendly and M == list(range(N)):
                    g2 = gamma2(G, A[typ0])
                    po = all(b not in g2[a] for a, b in itertools.combinations(R, 2))
                    assert po == (not bad); tally(('Thm B agrees', po))
                if kind == 'localdual' and not friendly:
                    assert not bad; tally(('Prop 6.4 repaired',))
    print(sorted(counts.items(), key=str))

    # Prop. 7.1: D -> H over Q(4,q), M = id, relaxed set T of lines; exact set of bad pairs; Prop. 7.2 with A-hubs
    for q in (3, 4, 5):
        F = GF(q); Qq = Q4(F); N = Qq.N
        for trial in range(6):
            T = []
            for l in rng.sample(range(N), N):          # greedy random relaxed set: each line meets <= 1 other
                if len(T) >= 3 * q:
                    break
                m_ = [m for m in T if m in Qq.meets[l]]
                if len(m_) == 0 or (len(m_) == 1 and not any(k in Qq.meets[m_[0]] for k in T if k != l)):
                    T.append(l)
            partner = {}
            for l in T:
                ms = [m for m in T if m in Qq.meets[l]]
                assert len(ms) <= 1
                if ms:
                    partner[l] = ms[0]
            bad = two_level_bad(Qq, 'D', 'H', list(range(N)), T)
            pred = set()
            for l, m in partner.items():
                z = (set(Qq.lp[l]) & set(Qq.lp[m])).pop()
                for p in Qq.lp[m]:
                    if p != z:
                        pred.add((N + l, p))       # (l, j) [line of level 0]  -  (p, j') [point of level 1]
                        pred.add((p, N + l))       # (p, j) [point of level 0] -  (l, j') [line of level 1]
            assert bad == pred, (q, len(bad), len(pred))
            assert len(pred) == 4 * q * len(partner) // 2
            # Prop. 7.2: an A-hub per partnered l, adjacent to (l, level 1) and to a point of the partner in level 0
            hubs_ok = [[(1, 'L', l), (0, 'P', rng.choice(Qq.lp[partner[l]]))] for l in partner]
            bad2 = two_level_bad(Qq, 'D', 'H', list(range(N)), T, hubs_ok)
            # the rule broken for one line: its hub's level-0 slot off the partner line
            if partner:
                l0 = next(iter(partner))
                off = rng.choice([p for p in range(N) if p not in Qq.lp[partner[l0]]])
                hubs_bad = [[(1, 'L', l), (0, 'P', off if l == l0 else rng.choice(Qq.lp[partner[l]]))] for l in partner]
                bad3 = two_level_bad(Qq, 'D', 'H', list(range(N)), T, hubs_bad)
            else:
                bad3 = set()
            print("q=%d |T|=%d pairs=%d: bad pairs %d = 4q*pairs (Prop 7.1 exact set: yes); with hub rule %d; rule broken at one line %d"
                  % (q, len(T), len(partner) // 2, len(bad), len(bad2), len(bad3)))
            assert not bad2

if __name__ == "__main__":
    main()
