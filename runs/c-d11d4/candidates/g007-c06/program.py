import itertools
import math
import random
import time

import numpy as np

import lib


# Bold new engine: abelian voltage lifts Z_m1 x Z_m2 over a bipartite base with K + K
# vertices and d perfect-matching darts per slot. Because the group acts by translation,
# distances from (u,x) equal distances from (u,0), so the diameter check needs only
# 2K BFS runs. Simulated annealing on voltages and slot permutations minimises the number
# of unreached pairs. Output is a deduplicated lift with an order above min_n.
C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define MAXNB (2 * MAXK)
#define MAXNT 60000

static uint64_t rs = 88172645463325252ULL;
static clock_t t0;
static double tlimit = 1.0;

static uint64_t rnd64(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0) / CLOCKS_PER_SEC; }
static int over(void) { return elapsed() >= tlimit; }

static int d, D, K, M1, M2, G, NB, NT;
static int P[MAXD][MAXK];
static int V[MAXD * MAXK];
static int incT[MAXNB][MAXD], incO[MAXNB][MAXD];
static int fillc[MAXNB];
static uint32_t vis[MAXNT];
static uint32_t stamp = 0;
static int qu[MAXNT];
static int xa[MAXNT], xb[MAXNT];

static void set_group(int m1, int m2, int g) {
    M1 = m1; M2 = m2; G = g;
    for (int e = 0; e < G; e++) { xa[e] = e / M2; xb[e] = e % M2; }
}

static int addg(int x, int y) {
    int a = xa[x] + xa[y]; if (a >= M1) a -= M1;
    int b = xb[x] + xb[y]; if (b >= M2) b -= M2;
    return a * M2 + b;
}

static int negg(int g) {
    int a = xa[g], b = xb[g];
    int na = a ? M1 - a : 0;
    int nb = b ? M2 - b : 0;
    return na * M2 + nb;
}

static void build_inc(void) {
    for (int b = 0; b < NB; b++) fillc[b] = 0;
    for (int s = 0; s < d; s++) {
        for (int i = 0; i < K; i++) {
            int t = s * K + i;
            int bb = K + P[s][i];
            int g = V[t];
            incT[i][fillc[i]] = bb; incO[i][fillc[i]] = g; fillc[i]++;
            incT[bb][fillc[bb]] = i; incO[bb][fillc[bb]] = negg(g); fillc[bb]++;
        }
    }
}

/* Total number of (source, vertex) pairs at distance > D, sources = (u, 0) for each base u. */
static long eval_cost(void) {
    build_inc();
    long unreached = 0;
    for (int u = 0; u < NB; u++) {
        stamp++;
        if (stamp == 0) { memset(vis, 0, sizeof(vis)); stamp = 1; }
        int head = 0, tail = 0;
        int s0 = u * G;
        qu[tail++] = s0; vis[s0] = stamp;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int lim = tail;
            while (head < lim) {
                int v = qu[head++];
                int b = v / G, x = v - b * G;
                for (int k = 0; k < d; k++) {
                    int w = incT[b][k] * G + addg(x, incO[b][k]);
                    if (vis[w] != stamp) { vis[w] = stamp; qu[tail++] = w; }
                }
            }
        }
        unreached += NT - tail;
    }
    return unreached;
}

static int anneal(long iters) {
    for (int s = 0; s < d; s++) {
        for (int i = 0; i < K; i++) P[s][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = P[s][i]; P[s][i] = P[s][j]; P[s][j] = tmp;
        }
    }
    for (int t = 0; t < d * K; t++) V[t] = rndint(G);
    long cur = eval_cost();
    for (long it = 0; it < iters && cur > 0; it++) {
        if ((it & 255) == 0 && over()) break;
        double temp = 1.5 * (1.0 - (double)it / (double)iters) + 0.05;
        if (rnd01() < 0.5) {
            int t = rndint(d * K);
            int nv = rndint(G);
            if (nv == V[t]) continue;
            int old = V[t];
            V[t] = nv;
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) cur = nc;
            else V[t] = old;
        } else {
            int s = rndint(d), i = rndint(K), j = rndint(K);
            if (i == j) continue;
            int tmp = P[s][i]; P[s][i] = P[s][j]; P[s][j] = tmp;
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / temp)) cur = nc;
            else { tmp = P[s][i]; P[s][i] = P[s][j]; P[s][j] = tmp; }
        }
    }
    return cur == 0;
}

static int cmp_ll(const void *a, const void *b) {
    long long x = *(const long long *)a, y = *(const long long *)b;
    return (x > y) - (x < y);
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    tlimit = atof(argv[4]) * 0.9;
    int min_n = argc > 5 ? atoi(argv[5]) : 1;
    if (d < 2 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    static int bestP[MAXD][MAXK];
    static int bestV[MAXD * MAXK];
    int bestNT = 0, bestK = 0, bestM1 = 0, bestM2 = 0, bestG = 0;

    t0 = clock();
    int target = min_n < 2 ? 2 : min_n;
    while (!over()) {
        K = 1 + rndint(6);
        int Gmin = (target + 2 * K - 1) / (2 * K);
        if (Gmin < 2) Gmin = 2;
        int G0 = Gmin + rndint(3);
        if (2 * K * G0 > MAXNT) continue;
        int divs[128], nd = 0;
        for (int m1 = 1; m1 * m1 <= G0; m1++) if (G0 % m1 == 0) divs[nd++] = m1;
        int m1 = divs[rndint(nd)];
        set_group(m1, G0 / m1, G0);
        NB = 2 * K;
        NT = NB * G;
        if (anneal(8000)) {
            bestNT = NT; bestK = K; bestM1 = M1; bestM2 = M2; bestG = G;
            memcpy(bestP, P, sizeof(P));
            memcpy(bestV, V, sizeof(V));
            target = NT + 1;
        }
    }

    if (bestNT == 0) { printf("0 0\n"); return 0; }

    K = bestK; NB = 2 * K;
    set_group(bestM1, bestM2, bestG);
    NT = NB * G;
    memcpy(P, bestP, sizeof(P));
    memcpy(V, bestV, sizeof(V));

    size_t cap = (size_t)K * d * G;
    long long *keys = (long long *)malloc(sizeof(long long) * cap);
    if (!keys) { printf("0 0\n"); return 0; }
    size_t m = 0;
    for (int s = 0; s < d; s++) {
        for (int i = 0; i < K; i++) {
            int t = s * K + i;
            int bb = K + P[s][i];
            int g = V[t];
            for (int x = 0; x < G; x++) {
                long long u = (long long)i * G + x;
                long long w = (long long)bb * G + addg(x, g);
                long long lo = u < w ? u : w;
                long long hi = u < w ? w : u;
                keys[m++] = lo * (long long)NT + hi;
            }
        }
    }
    qsort(keys, m, sizeof(long long), cmp_ll);
    size_t out = 0;
    for (size_t j = 0; j < m; j++) {
        if (out == 0 || keys[j] != keys[out - 1]) keys[out++] = keys[j];
    }
    printf("%d %zu\n", NT, out);
    for (size_t j = 0; j < out; j++) {
        printf("%lld %lld\n", keys[j] / NT, keys[j] % NT);
    }
    free(keys);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Base constructions.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q), order 2(q+1)(q^2+1)."""
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
    """W(q) for the largest prime power q with q + 1 <= d (q <= 16)."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Twin extension: a twin of x (same side, same neighbourhood) keeps all old
# distances and needs one spare degree on each neighbour of x.
# ----------------------------------------------------------------------------

def _twin_grow(n, edges, d, rng, deadline):
    edges = list(edges)
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    deg = [len(a) for a in adj]
    changed = True
    while changed and time.monotonic() < deadline:
        changed = False
        order = list(range(n))
        rng.shuffle(order)
        for x in order:
            if time.monotonic() >= deadline:
                break
            nb = adj[x]
            if not nb or any(deg[y] >= d for y in nb):
                continue
            v = n
            n += 1
            adj.append(list(nb))
            deg.append(len(nb))
            for y in nb:
                adj[y].append(v)
                deg[y] += 1
                edges.append((y, v))
            changed = True
    return n, edges


def _remove_twins(n, edges, frac, rng):
    """Delete a random fraction of redundant twins; this preserves all remaining distances."""
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    classes = {}
    for v in range(n):
        if adj[v]:
            classes.setdefault(frozenset(adj[v]), []).append(v)
    cands = []
    for grp in classes.values():
        if len(grp) >= 2:
            cands.extend(grp[1:])
    if not cands:
        return n, list(edges)
    k = max(1, int(frac * len(cands)))
    drop = set(rng.sample(cands, min(k, len(cands))))
    keep = [v for v in range(n) if v not in drop]
    idx = {v: i for i, v in enumerate(keep)}
    new_e = [(idx[u], idx[v]) for u, v in edges if u not in drop and v not in drop]
    return len(keep), new_e


# ----------------------------------------------------------------------------
# Cover helpers. A new vertex v on side c is at distance <= D from everything
# iff its neighbourhood S satisfies: every vertex lies within D-1 of some s in S.
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


def _cand_matrix(cand_balls, n):
    nb = (n + 7) // 8
    buf = b"".join(x.to_bytes(nb, "little") for x in cand_balls)
    arr = np.frombuffer(buf, dtype=np.uint8).reshape(len(cand_balls), nb)
    return np.unpackbits(arr, axis=1, bitorder="little")[:, :n].astype(bool)


def _weighted_cover(B, cand_ids, n, d, nrng, randomize):
    """Hardest-first weighted cover: rare uncovered vertices get larger weight."""
    k = B.shape[0]
    uncov = np.ones(n, dtype=bool)
    avail = np.ones(k, dtype=bool)
    chosen = []
    for _ in range(d):
        if not uncov.any():
            break
        sub = B[:, uncov]
        cnt = sub.sum(axis=0)
        if (cnt == 0).any():
            return None
        w = 1.0 / cnt
        score = sub.astype(np.float64) @ w
        if randomize:
            score = score * (1.0 + 0.08 * nrng.random(k))
        score[~avail] = -1.0
        i = int(np.argmax(score))
        if score[i] <= 0:
            break
        avail[i] = False
        chosen.append(cand_ids[i])
        uncov &= ~B[i]
    return chosen if not uncov.any() else None


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


def _local_cover(cands, ball, full, d, rng, iters, deadline):
    pool = list(cands)
    if not pool:
        return None
    k = min(d, len(pool))
    chosen = rng.sample(pool, k)
    union = 0
    for s in chosen:
        union |= ball[s]
    if union == full:
        return chosen
    score = union.bit_count()
    for _ in range(iters):
        if time.monotonic() >= deadline:
            break
        i = rng.randrange(k)
        s = rng.choice(pool)
        if s in chosen:
            continue
        trial = chosen[:]
        trial[i] = s
        u = 0
        for t in trial:
            u |= ball[t]
        sc = u.bit_count()
        if sc >= score:
            chosen, score = trial, sc
            if u == full:
                return chosen
    return None


def _find_cover(cands, ball, n, full, d, rng, deadline):
    B = _cand_matrix([ball[s] for s in cands], n)
    nrng = np.random.default_rng(rng.randrange(1 << 30))
    for attempt in range(12):
        if time.monotonic() >= deadline:
            return None
        chosen = _weighted_cover(B, cands, n, d, nrng, attempt > 0)
        if chosen:
            return chosen
    for attempt in range(60):
        if time.monotonic() >= deadline:
            return None
        chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
        if chosen:
            return chosen
    if time.monotonic() < deadline:
        return _local_cover(cands, ball, full, d, rng, 400, deadline)
    return None


def _extend_cover(n, edges, d, D, deadline, rng):
    """Append whole vertices whose neighbourhoods cover all vertices, using spare degree only."""
    if D < 2:
        return n, edges
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
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
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


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth, cover growth and edge saturation until nothing changes.

    Every step keeps diameter <= D and bipartiteness, so the output is valid
    whenever the input is.
    """
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def _gq_iterate(gq, d, D, end, rng, consider):
    """Repeatedly regrow from W(q) or from a twin-thinned version of the current state."""
    cur = None
    while time.monotonic() < end:
        if cur is None or rng.random() < 0.2:
            src_n, src_e = gq[0], gq[1]
        else:
            src_n, src_e = _remove_twins(cur[0], cur[1], 0.15, rng)
        pn, pe = _pipeline(src_n, src_e, d, D, end, rng)
        consider(pn, pe)
        if cur is None or pn >= cur[0]:
            cur = (pn, pe)


# ----------------------------------------------------------------------------
# Rewire-then-extend: temporarily delete a few random edges to free degree,
# try to attach a covering vertex, and keep the move only if the full graph
# still has diameter <= D (checked exactly).
# ----------------------------------------------------------------------------

def _edges_of(n, adj):
    return [(u, v) for u in range(n) for v in adj[u] if u < v]


def _rewire_extend(n, edges, d, D, deadline, rng):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _bipartition(n, [list(s) for s in adj])
    while time.monotonic() < deadline:
        c = rng.randrange(2)
        k = rng.choice((0, 1, 1, 2, 3))
        dropped = []
        for _ in range(k):
            s = rng.randrange(n)
            if not adj[s]:
                continue
            t = rng.choice(sorted(adj[s]))
            adj[s].discard(t)
            adj[t].discard(s)
            dropped.append((s, t))
        adj_l = [list(x) for x in adj]
        ball = _balls_radius(n, adj_l, D - 1)
        full = (1 << n) - 1
        cands = [s for s in range(n) if color[s] == 1 - c and len(adj[s]) < d]
        chosen = None
        if cands:
            chosen = _find_cover(cands, ball, n, full, d, rng, deadline)
        ok = False
        if chosen:
            v = n
            for s in chosen:
                adj[s].add(v)
            adj.append(set(chosen))
            n_new = n + 1
            if lib.bad_pairs(n_new, _edges_of(n_new, adj), D) == 0:
                n = n_new
                color.append(c)
                ok = True
            else:
                for s in chosen:
                    adj[s].discard(v)
                adj.pop()
        if not ok:
            for s, t in dropped:
                adj[s].add(t)
                adj[t].add(s)
    return n, _edges_of(n, adj)


# ----------------------------------------------------------------------------
# Secondary family: non-cyclic and cyclic voltage lifts (Python versions).
# ----------------------------------------------------------------------------

def _sample_group(G, rng):
    for _ in range(60):
        k2 = rng.randint(1, 12)
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 40))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _group_search(d, D, k, G, rng, iters, deadline):
    g = _sample_group(G, rng)
    if g is None:
        return None
    order, mul = g
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(order)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.group_lift(2 * k, [tuple(x) for x in darts], order, mul)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0 or time.monotonic() > deadline:
            break
        if order < 2:
            break
        j = rng.randrange(len(darts))
        old = darts[j][2]
        darts[j][2] = (old + rng.randrange(1, order)) % order
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _search_haar(d, D, m, rng, deadline, iters):
    others = list(range(1, m))
    if len(others) < d - 1:
        return None

    def cost(S):
        n, edges = lib.haar_graph(m, S)
        return lib.bad_pairs(n, edges, D)

    S = [0] + rng.sample(others, d - 1)
    c = cost(S)
    for _ in range(iters):
        if c == 0:
            return S
        if time.monotonic() >= deadline:
            break
        cand = [x for x in others if x not in S]
        if not cand:
            break
        i = rng.randrange(1, d)
        T = S[:]
        T[i] = rng.choice(cand)
        ct = cost(T)
        if ct <= c:
            S, c = T, ct
    return S if c == 0 else None


def _search_lift(d, D, k, m, rng, iters, deadline):
    perms = [rng.sample(range(k), k) for _ in range(d)]
    darts = [[i, k + p[i], rng.randrange(m)] for p in perms for i in range(k)]

    def evaluate():
        n, e = lib.voltage_lift(2 * k, [tuple(x) for x in darts], m)
        return n, e, lib.bad_pairs(n, e, D)

    n, e, c = evaluate()
    for _ in range(iters):
        if c == 0:
            break
        if time.monotonic() > deadline:
            break
        touched = [rng.randrange(len(darts))]
        if rng.random() < 0.2:
            touched.append(rng.randrange(len(darts)))
        olds = [(j, darts[j][2]) for j in touched]
        for j in touched:
            if m > 1:
                darts[j][2] = (darts[j][2] + rng.randrange(1, m)) % m
        n2, e2, c2 = evaluate()
        if c2 <= c:
            n, e, c = n2, e2, c2
        else:
            for j, old in olds:
                darts[j][2] = old
    if c == 0:
        return n, e
    return None


def _lift_loop(d, D, best_n, deadline, rng, consider):
    group_p = 0.3
    haar_p = 0.2 if D <= 4 else 0.15
    base_sizes = [1, 2, 3, 4, 5, 6]
    group_sizes = [1, 2, 3, 4]
    ladder = {k: 2 for k in base_sizes}
    group_state = {k: {"G": 1, "step": 1, "miss": 0} for k in group_sizes}
    haar_m, haar_miss = d + 1, 0
    cur_best = best_n
    while time.monotonic() < deadline:
        r = rng.random()
        if r < group_p:
            k = rng.choice(group_sizes)
            st = group_state[k]
            floor = cur_best // (2 * k) + 1
            G = max(st["G"], floor, 2)
            res = _group_search(d, D, k, G, rng, 200, deadline)
            if res is not None:
                consider(res[0], res[1])
                cur_best = max(cur_best, res[0])
                st["G"] = G + st["step"]
                st["step"] = min(st["step"] * 2, max(1, G // 10))
                st["miss"] = 0
            else:
                st["G"] = G
                st["miss"] += 1
                if st["miss"] >= 3:
                    st["step"] = 1
                    st["miss"] = 0
                    st["G"] = floor
        elif rng.random() < haar_p and haar_miss < 4:
            S = _search_haar(d, D, haar_m, rng, deadline, 120)
            if S is not None:
                n, e = lib.haar_graph(haar_m, S)
                consider(n, e)
                cur_best = max(cur_best, n)
                haar_miss = 0
            else:
                haar_miss += 1
            haar_m += 1
        else:
            k = rng.choice(base_sizes)
            m = max(ladder[k], cur_best // (2 * k) + 1, 2)
            res = _search_lift(d, D, k, m, rng, 250, deadline)
            if res is not None:
                consider(res[0], res[1])
                cur_best = max(cur_best, res[0])
                ladder[k] = m + 1
            else:
                ladder[k] = m


# ----------------------------------------------------------------------------
# Bold family: abelian lifts searched in C, asking for an order above min_n.
# ----------------------------------------------------------------------------

def _c_lift_search(d, D, seed, min_n, budget):
    """Run the C annealer for `budget` seconds; return a valid (n, edges) with n >= min_n, or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, int(seed), f"{budget:.2f}", int(min_n)],
                        timeout=budget + 3.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n <= 0 or not e or n < min_n:
        return None
    if lib.is_valid(n, e, d, D):
        return n, e
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    # Trivial cases.
    if d >= 1 and D == 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            pn, pe = _pipeline(pg[0], pg[1], d, D, start + 0.3 * time_limit, rng)
            consider(pn, pe)
            if time.monotonic() < start + 0.85 * time_limit:
                rn, re_ = _rewire_extend(best_n, best[1], d, D, start + 0.6 * time_limit, rng)
                consider(rn, re_)
        _lift_loop(d, D, best_n, start + 0.85 * time_limit, rng, consider)
        if not lib.is_valid(best[0], best[1], d, D):
            best = lib.haar_graph(d, range(d))
        return best

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            # Parent-style growth from W(q), now limited to half the budget.
            _gq_iterate(gq, d, D, start + 0.3 * time_limit, rng, consider)
            if time.monotonic() < start + 0.5 * time_limit:
                rn, re_ = _rewire_extend(best_n, best[1], d, D, start + 0.5 * time_limit, rng)
                consider(rn, re_)
        else:
            _lift_loop(d, D, best_n, start + 0.5 * time_limit, rng, consider)

        # Bold step: C annealer over abelian voltage lifts, aiming above the current best.
        remaining = time_limit * 0.93 - (time.monotonic() - start)
        budget = min(0.4 * time_limit, remaining - 4.0)
        if budget >= 3.0:
            res = _c_lift_search(d, D, seed, best_n + 1, budget)
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
