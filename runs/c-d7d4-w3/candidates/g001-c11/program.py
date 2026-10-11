import itertools
import math
import random
import time

import lib


# Search engine: hill-climb over bi-Cayley graphs BiCay(G, S), where G is a group of
# order m, S is a set of d elements of G, and left vertex x is joined to right vertex
# x*s for each s in S. Left multiplication is an automorphism, so the diameter check
# only needs BFS from one left and one right vertex. The stdin graph carries the group
# tables: the first G*G pairs are the multiplication table, the next G pairs are the inverses.
C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static int G, DD, DIAM;
static int *T;
static int *INV;
static uint32_t *stamp;
static uint32_t cur_stamp = 0;
static int *qbuf;
static uint64_t rs = 1;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static int in_set(const int *S, int k, int g) {
    for (int j = 0; j < k; j++) if (S[j] == g) return 1;
    return 0;
}

/* Number of (vertex, side) pairs NOT reached within DIAM from L_0 and from R_0. */
static int cost(const int *S) {
    int Sinv[64];
    for (int i = 0; i < DD; i++) Sinv[i] = INV[S[i]];
    int total = 0;
    for (int side = 0; side < 2; side++) {
        int start = (side == 0) ? 0 : G;
        cur_stamp++;
        if (cur_stamp == 0) {
            memset(stamp, 0, sizeof(uint32_t) * (size_t)(2 * G));
            cur_stamp = 1;
        }
        int head = 0, tail = 0;
        qbuf[tail++] = start;
        stamp[start] = cur_stamp;
        for (int lev = 0; lev < DIAM && head < tail; lev++) {
            int lend = tail;
            while (head < lend) {
                int v = qbuf[head++];
                if (v < G) {
                    const int *row = T + (size_t)v * G;
                    for (int i = 0; i < DD; i++) {
                        int w = G + row[S[i]];
                        if (stamp[w] != cur_stamp) {
                            stamp[w] = cur_stamp;
                            qbuf[tail++] = w;
                        }
                    }
                } else {
                    const int *row = T + (size_t)(v - G) * G;
                    for (int i = 0; i < DD; i++) {
                        int w = row[Sinv[i]];
                        if (stamp[w] != cur_stamp) {
                            stamp[w] = cur_stamp;
                            qbuf[tail++] = w;
                        }
                    }
                }
            }
        }
        total += 2 * G - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DD = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tlim = atof(argv[4]);
    int N, M;
    if (scanf("%d %d", &N, &M) != 2) { printf("NONE\n"); return 0; }
    G = N;
    if (G < DD || DD < 2 || DD > 60 || G < 1 || M < G * G + G) {
        printf("NONE\n");
        return 0;
    }
    int *P = malloc(sizeof(int) * 2 * (size_t)M);
    for (int i = 0; i < M; i++) {
        if (scanf("%d %d", &P[2 * i], &P[2 * i + 1]) != 2) { printf("NONE\n"); return 0; }
    }
    T = malloc(sizeof(int) * (size_t)G * G);
    INV = malloc(sizeof(int) * (size_t)G);
    for (int k = 0; k < G * G; k++) T[k] = P[2 * k];
    for (int i = 0; i < G; i++) INV[i] = P[2 * (G * G + i)];
    free(P);
    stamp = calloc((size_t)2 * G, sizeof(uint32_t));
    qbuf = malloc(sizeof(int) * (size_t)2 * G);
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 88172645463325252ULL;

    clock_t t0 = clock();
    int S[64], bestS[64];
    int bestc = 1000000000;
    int expired = 0;
    long long evals = 0;

    while (!expired) {
        S[0] = 0;
        int k = 1;
        while (k < DD) {
            int g = rndint(G);
            if (g != 0 && !in_set(S, k, g)) S[k++] = g;
        }
        int c = cost(S);
        int stall = 0;
        while (c > 0 && stall < 3000) {
            if (((++evals) & 15) == 0) {
                if ((double)(clock() - t0) / CLOCKS_PER_SEC > tlim) { expired = 1; break; }
            }
            int i = 1 + rndint(DD - 1);
            int g = rndint(G);
            if (g == 0 || in_set(S, DD, g)) continue;
            int old = S[i];
            S[i] = g;
            int c2 = cost(S);
            if (c2 <= c) {
                if (c2 < c) stall = 0; else stall++;
                c = c2;
            } else {
                S[i] = old;
                stall++;
            }
        }
        if (c < bestc) {
            bestc = c;
            memcpy(bestS, S, sizeof(int) * (size_t)DD);
        }
        if (bestc == 0) break;
    }

    if (bestc == 0) {
        printf("FOUND");
        for (int j = 0; j < DD; j++) printf(" %d", bestS[j]);
        printf("\n");
    } else {
        printf("NONE %d\n", bestc);
    }
    return 0;
}
'''


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q)."""
    F = lib.GF(q)
    pts = [v for v in itertools.product(range(q), repeat=4)
           if any(v) and next(c for c in v if c) == 1]
    index = {v: i for i, v in enumerate(pts)}
    P = len(pts)

    def norm(v):
        c = next(x for x in v if x)
        inv = F.inv(c)
        return tuple(F.mul(inv, x) for x in v)

    def form(x, y):
        t = F.sub(F.mul(x[0], y[1]), F.mul(x[1], y[0]))
        return F.add(t, F.sub(F.mul(x[2], y[3]), F.mul(x[3], y[2])))

    covered = set()
    lines = []
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            if (i, j) in covered:
                continue
            y = pts[j]
            if form(x, y) != 0:
                continue
            L = set()
            for a in range(q):
                for b in range(q):
                    if a == 0 and b == 0:
                        continue
                    v = tuple(F.add(F.mul(a, x[k]), F.mul(b, y[k])) for k in range(4))
                    if any(v):
                        L.add(index[norm(v)])
            L = sorted(L)
            lines.append(L)
            for p in L:
                for r in L:
                    if p < r:
                        covered.add((p, r))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """Generalized quadrangle incidence graph W(q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

def _balls_radius(n, adj, r):
    ball = [1 << v for v in range(n)]
    for _ in range(r):
        new = []
        for v in range(n):
            x = ball[v]
            for u in adj[v]:
                x |= ball[u]
            new.append(x)
        ball = new
    return ball


def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _to_sets(n, edges):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    return adj


def _greedy_cover(cands, ball, full, d, rng, randomize):
    pool = list(cands)
    if randomize:
        rng.shuffle(pool)
    covered = 0
    chosen = []
    while covered != full and len(chosen) < d and pool:
        gains = [(ball[s] & ~covered).bit_count() for s in pool]
        best_g = max(gains, default=0)
        if best_g == 0:
            break
        thr = best_g
        if randomize and rng.random() < 0.5:
            thr = best_g - 1
        opts = [i for i, g in enumerate(gains) if g >= thr and g > 0]
        i = rng.choice(opts) if randomize else opts[0]
        s = pool.pop(i)
        chosen.append(s)
        covered |= ball[s]
    return chosen if covered == full else None


def _extend_cover(n, edges, d, D, deadline, rng=None, attempts=200):
    if D < 2:
        return n, edges
    if rng is None:
        rng = random.Random(0)
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)

    while time.monotonic() < deadline:
        ball = _balls_radius(n, adj, D - 1)
        full = (1 << n) - 1
        added = False
        for c in (0, 1):
            cands = [s for s in range(n) if color[s] == c and deg[s] < d]
            if not cands:
                continue
            chosen = None
            for attempt in range(attempts):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if chosen:
                v = n
                n += 1
                color.append(1 - c)
                adj.append([])
                deg.append(0)
                for s in chosen:
                    edges.append((s, v))
                    adj[s].append(v)
                    adj[v].append(s)
                    deg[s] += 1
                    deg[v] += 1
                added = True
                break
        if not added:
            break
    return n, edges


def _saturate_edges(n, edges, d, rng):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    existing = set()
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
        existing.add((min(u, v), max(u, v)))
    deg = [len(a) for a in adj]
    color = _bipartition(n, adj)
    left = [v for v in range(n) if color[v] == 0 and deg[v] < d]
    right = [v for v in range(n) if color[v] == 1 and deg[v] < d]
    pairs = [(a, b) for a in left for b in right
             if (min(a, b), max(a, b)) not in existing]
    rng.shuffle(pairs)
    for a, b in pairs:
        if deg[a] < d and deg[b] < d:
            edges.append((a, b))
            deg[a] += 1
            deg[b] += 1
    return edges


def _grow(n, edges, d, D, deadline, rng, attempts=200):
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng, attempts)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


# ----------------------------------------------------------------------------
# Twin duplication.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    changed = True
    while changed:
        changed = False
        order = list(range(len(adj)))
        rng.shuffle(order)
        for v in order:
            nb = adj[v]
            if not nb or len(nb) > d:
                continue
            if any(len(adj[u]) >= d for u in nb):
                continue
            w = len(adj)
            adj.append(set(nb))
            for u in nb:
                adj[u].add(w)
            changed = True
    out = [(u, v) for u in range(len(adj)) for v in adj[u] if u < v]
    return len(adj), out


def _trial(base_n, base_e, d, D, rng, deadline):
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng, attempts=30)
    return n, e


# ----------------------------------------------------------------------------
# Large-neighbourhood search (kill, repair, regrow).
# ----------------------------------------------------------------------------

def _cost(adj, D):
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _add_vertex(adj, color, d, D, side, rng):
    n = len(adj)
    ball = _balls_radius(n, adj, D - 1)
    covered = 0
    chosen = []
    cands = [s for s in range(n) if color[s] == side]
    for _ in range(d):
        best_s, best_g = None, -1.0
        for s in cands:
            if s in chosen:
                continue
            g = (ball[s] & ~covered).bit_count() + 0.5 * rng.random()
            if g > best_g:
                best_s, best_g = s, g
        if best_s is None:
            break
        chosen.append(best_s)
        covered |= ball[best_s]
    v = n
    adj.append(set())
    color.append(1 - side)
    for s in chosen:
        if len(adj[s]) >= d:
            t = rng.choice(tuple(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
        adj[s].add(v)
        adj[v].add(s)
    return v


def _fill(adj, color, d, rng):
    n = len(adj)
    left = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    right = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    pairs = [(a, b) for a in left for b in right if b not in adj[a]]
    rng.shuffle(pairs)
    for a, b in pairs:
        if len(adj[a]) < d and len(adj[b]) < d and b not in adj[a]:
            adj[a].add(b)
            adj[b].add(a)


def _anneal(adj, color, d, D, rng, iters, deadline):
    cur = _cost(adj, D)
    side0 = [v for v in range(len(adj)) if color[v] == 0]
    for _ in range(iters):
        if cur == 0 or time.monotonic() > deadline:
            break
        a = rng.choice(side0)
        if not adj[a]:
            continue
        b = rng.choice(tuple(adj[a]))
        c = rng.choice(side0)
        if c == a or not adj[c]:
            continue
        e = rng.choice(tuple(adj[c]))
        if e in adj[a] or b in adj[c]:
            continue
        adj[a].discard(b)
        adj[b].discard(a)
        adj[c].discard(e)
        adj[e].discard(c)
        adj[a].add(e)
        adj[e].add(a)
        adj[c].add(b)
        adj[b].add(c)
        new = _cost(adj, D)
        if new <= cur or (new == cur + 1 and rng.random() < 0.1):
            cur = new
        else:
            adj[a].discard(e)
            adj[e].discard(a)
            adj[c].discard(b)
            adj[b].discard(c)
            adj[a].add(b)
            adj[b].add(a)
            adj[c].add(e)
            adj[e].add(c)
    return cur == 0


def _lns(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 3))
        if k >= cur_n:
            break
        kill = set(rng.sample(range(cur_n), k))
        keep = [v for v in range(cur_n) if v not in kill]
        remap = {v: i for i, v in enumerate(keep)}
        m = len(keep)
        e2 = [(remap[u], remap[v]) for u, v in cur_e if u not in kill and v not in kill]
        adj = _to_sets(m, e2)
        color = _bipartition(m, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 150, deadline):
            continue
        e3 = [(u, v) for u in range(m) for v in adj[u] if u < v]
        n4, e4 = _grow(m, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Random bipartite 2-lifts, repaired by annealing.
# ----------------------------------------------------------------------------

def _random_lift2(n, edges, rng):
    out = []
    for u, v in edges:
        s = rng.randrange(2)
        for i in range(2):
            out.append((u + n * i, v + n * (i ^ s)))
    return 2 * n, out


def _lift_search(n, edges, d, D, deadline, rng, consider):
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        n2, e2 = _random_lift2(cur_n, cur_e, rng)
        adj = _to_sets(n2, e2)
        color = _bipartition(n2, adj)
        _fill(adj, color, d, rng)
        if not _anneal(adj, color, d, D, rng, 400, deadline):
            continue
        e3 = [(u, v) for u in range(n2) for v in adj[u] if u < v]
        n4, e4 = _grow(n2, e3, d, D, deadline, rng, attempts=16)
        consider(n4, e4)
        if n4 > cur_n and lib.is_valid(n4, e4, d, D):
            cur_n, cur_e = n4, e4


def _repair(d, D, n, edges, deadline, rng, consider):
    adj = _to_sets(n, edges)
    color = _bipartition(n, adj)
    while time.monotonic() < deadline:
        snap_adj = [set(s) for s in adj]
        snap_color = list(color)
        side = rng.randrange(2)
        _add_vertex(adj, color, d, D, side, rng)
        _fill(adj, color, d, rng)
        if _anneal(adj, color, d, D, rng, 1500, deadline):
            m = len(adj)
            e = [(u, v) for u in range(m) for v in adj[u] if u < v]
            consider(m, e)
        else:
            adj[:] = snap_adj
            color[:] = snap_color


# ----------------------------------------------------------------------------
# Bi-Cayley search: left x ~ right x*s for s in S, over groups of order m.
# ----------------------------------------------------------------------------

def _groups(m):
    """Candidate groups of order m: cyclic, and Z_mp x| Z_k with small r (r = 1 gives direct products)."""
    out = [lib.cyclic_group(m)]
    for k in range(2, m):
        if m % k:
            continue
        mp = m // k
        if mp < 2:
            continue
        for r in range(1, mp):
            if len(out) >= 8:
                return out
            if math.gcd(r, mp) == 1 and pow(r, k, mp) == 1 % mp:
                try:
                    out.append(lib.semidirect_group(mp, k, r))
                except ValueError:
                    pass
    return out


def _bicayley_try(d, D, group, seed, budget):
    """Run the C hill-climb on one group. Returns verified edges of the 2m-vertex graph, or None."""
    order, mul, inv = group
    rng_ = range(order)
    T = [mul(x, y) for x in rng_ for y in rng_]
    I = [inv(x) for x in rng_]
    edges = [(t, 0) for t in T] + [(i, 0) for i in I]
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}"],
                        stdin_graph=(order, edges), timeout=budget + 15.0)
    except RuntimeError:
        return None
    tok = out.split()
    if len(tok) < d + 1 or tok[0] != "FOUND":
        return None
    S = [int(t) for t in tok[1:1 + d]]
    e = [(x, order + mul(x, s)) for x in rng_ for s in S]
    if lib.is_valid(2 * order, e, d, D):
        return e
    return None


def _bicayley_sweep(d, D, m_lo, m_hi, seed, deadline):
    """Ascend through group orders m; stop at the first m where no group succeeds in its budget."""
    best = None
    m = m_lo
    while m <= m_hi:
        if deadline - time.monotonic() < 1.0:
            break
        found = None
        for gi, grp in enumerate(_groups(m)):
            remaining = deadline - time.monotonic()
            if remaining < 1.0:
                break
            budget = min(2.0, 0.3 * remaining)
            found = _bicayley_try(d, D, grp, seed * 7919 + m * 31 + gi, budget)
            if found is not None:
                break
        if found is None:
            break
        best = (m, found)
        m += 1
    return best


# ----------------------------------------------------------------------------
# Heuristic pipeline (previous approach), used as a second source of candidates.
# ----------------------------------------------------------------------------

def _heuristic(d, D, seed, time_limit):
    start = time.monotonic()
    deadline = start + 0.85 * time_limit
    rng = random.Random(seed)

    best_n, best_e = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)

    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            consider(n0, e0)
            base_n, base_e = n0, list(e0)
            grow_end = start + 0.15 * time_limit
            n1, e1 = _grow(n0, e0, d, D, grow_end, rng)
            consider(n1, e1)

    if D >= 2:
        trial_end = start + 0.25 * time_limit
        while time.monotonic() < trial_end:
            n, e = _trial(base_n, base_e, d, D, rng, trial_end)
            consider(n, e)

    if D >= 2 and time.monotonic() < deadline:
        lns_end = start + 0.45 * time_limit
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        lift_end = start + 0.70 * time_limit
        _lift_search(best_n, best_e, d, D, lift_end, rng, consider)

    if D >= 2 and time.monotonic() < deadline:
        _repair(d, D, best_n, best_e, deadline, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + 0.85 * time_limit

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    cap = lib.moore_bound(d, D)
    # Safe fallback: K_{d,d}, valid for D >= 2 and Moore-optimal for D = 2.
    best_n, best_e = lib.haar_graph(d, range(d))
    if not lib.is_valid(best_n, best_e, d, D):
        best_n, best_e = 2, [(0, 1)]
    if D == 2 or best_n >= cap:
        return best_n, list(best_e)

    if D == 3:
        base = _best_pg(d)
        if base is not None and base[0] > best_n and lib.is_valid(base[0], base[1], d, D):
            best_n, best_e = base[0], list(base[1])
            if best_n >= cap:
                return best_n, list(best_e)

    # Stage 1: heuristic pipeline (previous parent), a fraction of the budget.
    h_n, h_e = _heuristic(d, D, seed, 0.45 * time_limit)
    if h_n > best_n and lib.is_valid(h_n, h_e, d, D):
        best_n, best_e = h_n, list(h_e)
    if best_n >= cap:
        return best_n, list(best_e)

    # Stage 2 (new family): bi-Cayley hill-climb over groups of growing order m.
    if d >= 3 and D >= 2 and time.monotonic() < hard_end - 2.0:
        m_hi = cap // 2
        m_lo = max(d, int(0.66 * m_hi))
        if m_lo <= m_hi:
            try:
                res = _bicayley_sweep(d, D, m_lo, m_hi, seed, hard_end)
            except (RuntimeError, ValueError):
                res = None
            if res is not None:
                m, e = res
                if 2 * m > best_n and lib.is_valid(2 * m, e, d, D):
                    best_n, best_e = 2 * m, list(e)

    if not lib.is_valid(best_n, best_e, d, D):
        return lib.haar_graph(d, range(d))
    return best_n, list(best_e)
