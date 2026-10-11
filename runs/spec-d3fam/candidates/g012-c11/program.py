"""Bold change for D=3 targets: search for a Haar graph H(G, S) over an abelian group G.

Vertices a_x and b_x (x in G) with a_x ~ b_{x+s} for s in S, |S| = d. The graph is bipartite
and d-regular. It has diameter <= 3 when S-S covers G \\ {0} and S-S+S covers G, so the search
looks for a difference covering of G with |S| = d. Larger groups give larger graphs.

The Araujo-Pardo-Lopez / projective-plane base is kept as the fallback and is returned
unless a strictly larger valid graph is found.
"""
import math
import random
import time

import lib


def _color(n, adj):
    """Two-colour a bipartite graph given as adjacency sets (BFS/DFS from each unseen vertex)."""
    col = [-1] * n
    for s in range(n):
        if col[s] != -1:
            continue
        col[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if col[v] == -1:
                    col[v] = 1 - col[u]
                    stack.append(v)
    return col


def _bad_count(n, adj, D):
    """Ordered count of vertex pairs at distance > D (bitmask BFS), computed from adjacency sets."""
    reach = [1 << v for v in range(n)]
    for _ in range(D):
        new = []
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new.append(r)
        reach = new
    return sum(n - r.bit_count() for r in reach)


def _moore(d, D):
    """Moore-type upper bound on the order of a bipartite graph with max degree d and diameter D."""
    if D == 0 or d == 0:
        return 1
    if d == 1:
        return min(2, D + 1)
    if d == 2:
        return 2 * D
    return 2 * sum((d - 1) ** i for i in range(D))


def _augment(n, edges, d, D, rng, deadline):
    """Add two new vertices (a point P and a line L) using degree-preserving edge switches.

    Step 1: pick a matching of d edges (a_i, b_i); replace each by (a_i, P) and (b_i, L).
            Degrees of all old vertices are unchanged and P, L get degree d.
    Step 2: anneal with 2-switches (a,b),(c,e) -> (a,e),(c,b), which keep degrees and
            bipartiteness, minimising the number of pairs at distance > D.
    Returns (n+2, edges) with diameter <= D, or None if the search fails before the deadline.
    """
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    col = _color(n, adj)

    P, L = n, n + 1
    adj.append(set())
    adj.append(set())
    N = n + 2

    oriented = [((u, v) if col[u] == 0 else (v, u)) for u, v in edges]
    rng.shuffle(oriented)
    used, pick = set(), []
    for idx, (a, b) in enumerate(oriented):
        if a not in used and b not in used:
            pick.append(idx)
            used.add(a)
            used.add(b)
            if len(pick) == d:
                break
    if len(pick) < d:
        return None

    picked = set(pick)
    E = [oriented[i] for i in range(len(oriented)) if i not in picked]
    for idx in pick:
        a, b = oriented[idx]
        adj[a].discard(b)
        adj[b].discard(a)
        adj[a].add(P)
        adj[P].add(a)
        adj[b].add(L)
        adj[L].add(b)
        E.append((a, P))
        E.append((L, b))

    M = len(E)
    cur = _bad_count(N, adj, D)
    T = 1.0
    while cur > 0:
        if time.monotonic() >= deadline:
            return None
        i = rng.randrange(M)
        j = rng.randrange(M)
        if i == j:
            continue
        a, b = E[i]
        c, e = E[j]
        if a == c or b == e or e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b); adj[b].discard(a)
        adj[c].discard(e); adj[e].discard(c)
        adj[a].add(e); adj[e].add(a)
        adj[c].add(b); adj[b].add(c)
        new = _bad_count(N, adj, D)
        if new <= cur or rng.random() < math.exp((cur - new) / T):
            cur = new
            E[i] = (a, e)
            E[j] = (c, b)
        else:
            adj[a].discard(e); adj[e].discard(a)
            adj[c].discard(b); adj[b].discard(c)
            adj[a].add(b); adj[b].add(a)
            adj[c].add(e); adj[e].add(c)
    return N, list(E)


# ------------------------------------------------------------ abelian Haar search

def _divisors(m):
    """Divisors a of m with 2 <= a <= sqrt(m)."""
    return [a for a in range(2, math.isqrt(m) + 1) if m % a == 0]


def _group_data(mods):
    """Tables for the abelian group Z_mods[0] x Z_mods[1] x ...; element x has digit tuple dig[x]."""
    m = 1
    for a in mods:
        m *= a
    dig = []
    for x in range(m):
        v, t = [], x
        for md in reversed(mods):
            v.append(t % md)
            t //= md
        dig.append(tuple(reversed(v)))

    def enc(v):
        r = 0
        for c, md in zip(v, mods):
            r = r * md + c
        return r

    SUB = [[enc([(a - b) % md for a, b, md in zip(dig[x], dig[y], mods)])
             for y in range(m)] for x in range(m)]
    return m, mods, dig, enc, SUB


def _covers_triples(S, grp):
    """True if S - S + S covers the whole group."""
    m, mods, dig, enc, SUB = grp
    diffs = {0}
    for s in S:
        for t in S:
            if s != t:
                diffs.add(SUB[s][t])
    got = set()
    for e in diffs:
        ve = dig[e]
        for u in S:
            got.add(enc([(a + b) % md for a, b, md in zip(ve, dig[u], mods)]))
    return len(got) == m


def _find_S(grp, d, rng, deadline):
    """Simulated annealing for S (|S| = d, 0 in S) with S - S covering all nonzero elements."""
    m, mods, dig, enc, SUB = grp
    while time.monotonic() < deadline:
        S = [0] + rng.sample(range(1, m), d - 1)
        cnt = [0] * m
        for x in S:
            for y in S:
                if x != y:
                    cnt[SUB[x][y]] += 1
        unc = sum(1 for g in range(1, m) if cnt[g] == 0)
        best, stall = unc, 0
        while unc > 0:
            if time.monotonic() >= deadline:
                return None
            stall += 1
            if stall > 30000:
                break  # restart from a fresh random S
            i = rng.randrange(1, d)
            y = rng.randrange(1, m)
            if y in S:
                continue
            x = S[i]
            others = [t for t in S if t != x]
            old = unc
            # remove x
            for t in others:
                g = SUB[x][t]
                cnt[g] -= 1
                if cnt[g] == 0:
                    unc += 1
                g = SUB[t][x]
                cnt[g] -= 1
                if cnt[g] == 0:
                    unc += 1
            # add y
            for t in others:
                g = SUB[y][t]
                if cnt[g] == 0:
                    unc -= 1
                cnt[g] += 1
                g = SUB[t][y]
                if cnt[g] == 0:
                    unc -= 1
                cnt[g] += 1
            delta = unc - old
            if delta <= 0 or rng.random() < math.exp(-delta / 0.35):
                S[i] = y
                if unc < best:
                    best, stall = unc, 0
            else:
                for t in others:
                    cnt[SUB[y][t]] -= 1
                    cnt[SUB[t][y]] -= 1
                for t in others:
                    cnt[SUB[x][t]] += 1
                    cnt[SUB[t][x]] += 1
                unc = old
        if unc == 0 and _covers_triples(S, grp):
            return S
    return None


def _haar_from_S(S, grp):
    """Haar graph: a_x ~ b_{x+s} for s in S, vertices a_x = x and b_x = m + x."""
    m, mods, dig, enc, _ = grp
    edges = []
    for x in range(m):
        vx = dig[x]
        for s in S:
            y = enc([(a + b) % md for a, b, md in zip(vx, dig[s], mods)])
            edges.append((x, m + y))
    return 2 * m, edges


def _difference_search(d, D, base_n, rng, deadline):
    """Find a valid Haar graph with more than base_n vertices, trying orders m upward.

    Returns (n, edges) for the largest order found, or None.
    """
    mb = _moore(d, D)
    mmax = d * (d - 1) + 1
    m = base_n // 2 + 1
    best = None
    while time.monotonic() < deadline and m <= mmax and 2 * m <= mb:
        mods_list = [(m,)] + [(a, m // a) for a in _divisors(m)]
        found = None
        for k, mods in enumerate(mods_list):
            now = time.monotonic()
            if now >= deadline:
                break
            share = (deadline - now) / (len(mods_list) - k)
            grp = _group_data(mods)
            S = _find_S(grp, d, rng, time.monotonic() + share)
            if S is not None and _covers_triples(S, grp):
                n, edges = _haar_from_S(S, grp)
                if lib.is_valid(n, edges, d, D):
                    found = (n, edges)
                    break
        if found is None:
            break
        best = found
        m += 1
    return best


# ---------------------------------------------------------------- main entry

def build(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    # Structured bases for D = 3.
    base = None
    q = d - 1
    if D == 3 and q >= 2 and lib.is_prime_power(q):
        base = lib.projective_plane_incidence(q)          # order 2(q^2+q+1), degree q+1
    elif D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        base = lib.araujo_lopez_graph(d - 2)              # order 2(q^2+q+5), degree q+2 = d

    if base is not None:
        n, edges = base
        if lib.is_valid(n, edges, d, D):
            cur = (n, edges)
            if D == 3:
                try:
                    big = _difference_search(d, D, n, rng, start + 0.7 * time_limit)
                except Exception:
                    big = None
                if big is not None and big[0] > cur[0] and lib.is_valid(big[0], big[1], d, D):
                    cur = big
            mb = _moore(d, D)
            # Repeatedly try to grow by two vertices while time and the Moore bound allow.
            while time.monotonic() < deadline and cur[0] + 2 <= mb:
                res = _augment(cur[0], cur[1], d, D, rng, deadline)
                if res is None:
                    break
                if not lib.is_valid(res[0], res[1], d, D):
                    break
                cur = res
            return cur

    # Fallback: random Haar graphs (parent approach).
    best = lib.haar_graph(d, range(d))          # complete bipartite K_{d,d}: always valid
    m, misses = d + 1, 0
    while time.monotonic() < deadline and misses < 10:
        found = None
        for _ in range(30):
            if time.monotonic() >= deadline:
                break
            S = [0] + rng.sample(range(1, m), d - 1)
            n, edges = lib.haar_graph(m, S)
            if lib.within_diameter(n, edges, D):
                found = (n, edges)
                break
        if found:
            best, misses = found, 0
        else:
            misses += 1
        m += 1
    return best
