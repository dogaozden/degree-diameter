import itertools
import math
import random
import time

import numpy as np

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley search. Vertices A_g = g and B_h = N + h, with g, h in a
# group G of order N = m*k, the semidirect product Z_m x| Z_k (element a*k+b,
# (a,b)(c,e) = (a + r^b c, b+e)). Edges: A_g ~ B_{g s} for s in S, |S| = d.
# Left translation is an automorphism, so the diameter is the max eccentricity
# of A_e and B_e (two BFS). Hill-climb S to minimise the number of vertices
# farther than D from A_e or B_e. Order increases on each success.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double cpu_now(void) {
    return (double)clock() / (double)CLOCKS_PER_SEC;
}

static long long gcd_ll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int d_, D_;
static int cap = 0;
static int N_;
static int *mt = NULL;
static int *invt = NULL;
static int *S = NULL;
static int *dist = NULL;
static int *queue = NULL;
static char *in_set = NULL;

static int bestN = 0;
static int bestEdges = 0;
static int *bestE = NULL;

static void ensure_cap(int N) {
    if (N <= cap) return;
    free(mt);
    free(invt);
    free(S);
    free(dist);
    free(queue);
    free(in_set);
    cap = N;
    mt = malloc(sizeof(int) * (size_t)N * (size_t)N);
    invt = malloc(sizeof(int) * (size_t)N);
    S = malloc(sizeof(int) * (size_t)d_);
    dist = malloc(sizeof(int) * (size_t)(2 * N));
    queue = malloc(sizeof(int) * (size_t)(2 * N));
    in_set = malloc((size_t)N);
}

/* Multiplication table of Z_m x|_r Z_k, element code a*k + b. Identity is 0. */
static void build_group(int m, int k, int r) {
    int N = m * k;
    int *pw = malloc(sizeof(int) * (size_t)k);
    for (int b = 0; b < k; b++) pw[b] = (int)powmod_ll(r, b, m);
    for (int x = 0; x < N; x++) {
        int a1 = x / k, b1 = x % k;
        for (int y = 0; y < N; y++) {
            int a2 = y / k, b2 = y % k;
            int a = (int)(((long long)a1 + (long long)pw[b1] * a2) % m);
            int b = (b1 + b2) % k;
            mt[(size_t)x * N + y] = a * k + b;
        }
    }
    for (int x = 0; x < N; x++) {
        for (int y = 0; y < N; y++) {
            if (mt[(size_t)x * N + y] == 0) {
                invt[x] = y;
                break;
            }
        }
    }
    free(pw);
}

/* Number of vertices farther than D_ from A_e or B_e (0 iff valid). */
static int bfs_cost(void) {
    int N = N_;
    int V = 2 * N;
    int c = 0;
    int srcs[2] = {0, N};
    for (int si = 0; si < 2; si++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int qh = 0, qt = 0;
        dist[srcs[si]] = 0;
        queue[qt++] = srcs[si];
        while (qh < qt) {
            int u = queue[qh++];
            int du = dist[u];
            if (u < N) {
                int g = u;
                for (int i = 0; i < d_; i++) {
                    int w = N + mt[(size_t)g * N + S[i]];
                    if (dist[w] < 0) {
                        dist[w] = du + 1;
                        queue[qt++] = w;
                    }
                }
            } else {
                int h = u - N;
                for (int i = 0; i < d_; i++) {
                    int w = mt[(size_t)h * N + invt[S[i]]];
                    if (dist[w] < 0) {
                        dist[w] = du + 1;
                        queue[qt++] = w;
                    }
                }
            }
        }
        for (int v = 0; v < V; v++) {
            if (dist[v] < 0 || dist[v] > D_) c++;
        }
    }
    return c;
}

static void record_best(void) {
    int N = N_;
    free(bestE);
    bestE = malloc(sizeof(int) * 2 * (size_t)N * (size_t)d_);
    int cnt = 0;
    for (int g = 0; g < N; g++) {
        for (int i = 0; i < d_; i++) {
            bestE[2 * cnt] = g;
            bestE[2 * cnt + 1] = N + mt[(size_t)g * N + S[i]];
            cnt++;
        }
    }
    bestEdges = cnt;
    bestN = N;
}

static int try_group(int m, int k, int r, int iters, double t_end) {
    int N = m * k;
    if (N <= d_) return 0;
    ensure_cap(N);
    N_ = N;
    build_group(m, k, r);
    memset(in_set, 0, (size_t)N);
    for (int i = 0; i < d_; i++) {
        int x;
        do {
            x = rndint(N);
        } while (in_set[x]);
        S[i] = x;
        in_set[x] = 1;
    }
    int c = bfs_cost();
    for (int it = 0; it < iters && c > 0; it++) {
        if ((it & 31) == 0 && cpu_now() > t_end) break;
        int i = rndint(d_);
        int x;
        do {
            x = rndint(N);
        } while (in_set[x]);
        int old = S[i];
        in_set[old] = 0;
        in_set[x] = 1;
        S[i] = x;
        int c2 = bfs_cost();
        if (c2 <= c) {
            c = c2;
        } else {
            in_set[x] = 0;
            in_set[old] = 1;
            S[i] = old;
        }
    }
    if (c != 0) return 0;
    record_best();
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed time Nmin\n");
        return 1;
    }
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    double tl = atof(argv[4]);
    int Nmin = atoi(argv[5]);
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    double t_end = cpu_now() + tl;
    if (d_ < 2 || D_ < 2) {
        printf("0 0\n");
        return 0;
    }
    int N = Nmin > d_ + 1 ? Nmin : d_ + 1;
    while (cpu_now() < t_end) {
        int ok = 0;
        for (int tries = 0; tries < 40 && !ok && cpu_now() < t_end; tries++) {
            int divs[256];
            int nd = 0;
            for (int k = 1; k <= N && nd < 256; k++) {
                if (N % k == 0) divs[nd++] = k;
            }
            int k = divs[rndint(nd)];
            int m = N / k;
            int r = 0;
            if (m > 1) {
                int found = 0;
                for (int t = 0; t < 300 && !found; t++) {
                    int cand = 1 + rndint(m - 1);
                    if (gcd_ll(cand, m) == 1 && powmod_ll(cand, k, m) == 1 % m) {
                        r = cand;
                        found = 1;
                    }
                }
                if (!found) r = 1;
            }
            ok = try_group(m, k, r, 1500, t_end);
        }
        if (ok) N = N + 1;
    }
    if (bestEdges == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * bestN, bestEdges);
    for (int i = 0; i < bestEdges; i++) {
        printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions: generalized quadrangle W(q), projective planes, and
# twin / cover / saturation growth. Every step preserves diameter and bipartiteness.
# ----------------------------------------------------------------------------

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q).

    Points are all points of PG(3, q); lines are totally isotropic lines of the
    symplectic form B(x, y) = x0*y1 - x1*y0 + x2*y3 - x3*y2. Degree is q + 1,
    diameter is 4, and the order is 2(q+1)(q^2+1).
    """
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


def _twin_grow(n, edges, d, rng, deadline):
    """Add twin vertices while every neighbour of the original vertex has spare degree."""
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
    """Delete a random fraction of redundant twins; the diameter is preserved."""
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


def _balls_radius(n, adj, r):
    """Bitmask per vertex of all vertices within distance r."""
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
    """Two-colouring of a bipartite graph given by adjacency lists."""
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


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns the list or None."""
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


def _ball_rows(ball, idx, n):
    """float32 membership matrix: row r is the ball (0/1 over n vertices) of idx[r]."""
    nb = (n + 7) // 8
    out = np.zeros((len(idx), n), dtype=np.float32)
    for r, s in enumerate(idx):
        arr = np.frombuffer(ball[s].to_bytes(nb, "little"), dtype=np.uint8)
        out[r] = np.unpackbits(arr, bitorder="little")[:n]
    return out


def _weighted_cover(sub, cands, n, d, rng, randomize):
    """Rarity-weighted greedy cover of all n vertices by at most d candidate rows."""
    k = sub.shape[0]
    uncovered = np.ones(n, dtype=np.float32)
    avail_b = np.ones(k, dtype=bool)
    chosen = []
    while uncovered.sum() > 0:
        if len(chosen) >= d or not avail_b.any():
            return None
        avail = avail_b.astype(np.float32)
        cnt = avail @ sub
        if np.any((uncovered > 0) & (cnt < 0.5)):
            return None
        w = np.where(uncovered > 0, 1.0 / np.maximum(cnt, 1.0), 0.0).astype(np.float32)
        gain = sub @ w
        gain[~avail_b] = -1.0
        best = float(gain.max())
        if best <= 0:
            return None
        if randomize:
            thr = best * (0.9 if rng.random() < 0.3 else 1.0)
            opts = np.flatnonzero((gain >= thr) & avail_b)
            i = int(opts[rng.randrange(len(opts))])
        else:
            i = int(np.argmax(gain))
        chosen.append(cands[i])
        avail_b[i] = False
        uncovered[sub[i] > 0] = 0.0
    return chosen


def _weighted_cover_search(cands, ball, n, d, rng, tries, deadline):
    """Try several weighted covers (first deterministic, then randomised)."""
    sub = _ball_rows(ball, cands, n)
    for t in range(tries):
        if time.monotonic() >= deadline:
            break
        ch = _weighted_cover(sub, cands, n, d, rng, t > 0)
        if ch:
            return ch
    return None


def _extend_cover(n, edges, d, D, deadline, rng=None):
    """Greedily add vertices whose neighbourhoods are cover sets of deficient vertices."""
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
            for attempt in range(40):
                if time.monotonic() >= deadline:
                    break
                chosen = _greedy_cover(cands, ball, full, d, rng, attempt > 0)
                if chosen:
                    break
            if not chosen and time.monotonic() < deadline:
                chosen = _weighted_cover_search(cands, ball, n, d, rng, 15, deadline)
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
    """Greedily join deficient opposite-side vertices in random order. Returns new edge list."""
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


def _grow(n, edges, d, D, deadline, rng):
    """Extend by cover vertices, then saturate edges with the remaining spare degree."""
    cur_n, cur_e = n, list(edges)
    for _ in range(8):
        if time.monotonic() >= deadline:
            break
        n2, e2 = _extend_cover(cur_n, cur_e, d, D, deadline, rng)
        grew = n2 != cur_n
        cur_n = n2
        cur_e = _saturate_edges(cur_n, e2, d, rng)
        if not grew:
            break
    return cur_n, cur_e


def _pipeline(n, edges, d, D, deadline, rng):
    """Alternate twin growth and cover growth until neither adds a vertex."""
    cur_n, cur_e = n, list(edges)
    for _ in range(10):
        if time.monotonic() >= deadline:
            break
        before = cur_n
        cur_n, cur_e = _twin_grow(cur_n, cur_e, d, rng, deadline)
        cur_n, cur_e = _grow(cur_n, cur_e, d, D, deadline, rng)
        if cur_n == before:
            break
    return cur_n, cur_e


def _bicayley_search(d, D, seed, budget, n_min):
    """Run the C bi-Cayley search for about `budget` seconds. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), n_min],
                        timeout=budget + 15.0)
        n, e = lib.parse_graph_text(out)
    except Exception:
        return None
    if n <= 0 or not e:
        return None
    return n, e


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

    py_deadline = start + 0.5 * time_limit

    # D >= 3: projective planes for the few largest prime powers q with q + 1 <= d.
    if D >= 3:
        pg_qs = [q for q in range(d - 1, 1, -1) if lib.is_prime_power(q)][:3]
        if pg_qs:
            t0 = time.monotonic()
            span = max(0.0, py_deadline - t0)
            for i, q in enumerate(pg_qs):
                pg_n, pg_e = lib.projective_plane_incidence(q)
                consider(pg_n, pg_e)
                slice_end = t0 + span * (i + 1) / len(pg_qs)
                n2, e2 = _pipeline(pg_n, pg_e, d, D, slice_end, rng)
                consider(n2, e2)

    # D >= 4: grow the generalized quadrangle W(q) with twin/cover pipelines.
    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            cur = None
            top = None
            while time.monotonic() < py_deadline:
                if cur is None or rng.random() < 0.3:
                    src_n, src_e = gq[0], gq[1]
                else:
                    src_n, src_e = _remove_twins(cur[0], cur[1], rng.uniform(0.05, 0.4), rng)
                    src_e = _saturate_edges(src_n, src_e, d, rng)
                pn, pe = _pipeline(src_n, src_e, d, D, py_deadline, rng)
                consider(pn, pe)
                if top is None or pn > top[0]:
                    top = (pn, pe)
                if cur is None or pn >= cur[0] or rng.random() < 0.15:
                    cur = (pn, pe)
                if cur[0] < top[0] - 4:
                    cur = top

    # D >= 4: bi-Cayley search in C over semidirect-product groups, starting just
    # above half the current best order.
    if D >= 4 and d >= 3:
        remaining = start + 0.88 * time_limit - time.monotonic() - 2.0
        if remaining > 3.0:
            res = _bicayley_search(d, D, seed, remaining, max(d + 1, best_n // 2 + 1))
            if res is not None:
                consider(res[0], res[1])

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
