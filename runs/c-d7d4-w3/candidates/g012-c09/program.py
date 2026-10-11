import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: voltage-lift annealing over cyclic and semidirect groups Z_m x| Z_k.
#
# Base: a A-vertices and a B-vertices, d darts per base vertex. Dart (i, j, g)
# joins A(i,x) to B(j, x*g). Left translation is an automorphism, so the diameter
# test only needs one BFS from each of the 2a representatives A(i,e), B(j,e).
# Cost = number of (representative, vertex) pairs at distance > D. Zero cost means
# a valid lift. Runs that time out are parked and resumed later.
# Output: "N M" and M edges of the best lift with N > best_n, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 16
#define MAXA 4
#define MAXK (MAXA * MAXD)
#define MAXPARK 32
#define MAXSPEC 4096
#define NCAP_MAX 4000

typedef struct { int m, k, r; } Spec;

typedef struct {
    int a, G, m, k, r;
    int dst[MAXK];
    int gv[MAXK];
    double T;
    long long cur;
} Run;

static uint32_t rs = 2463534242u;

static uint32_t rnd32(void) {
    rs ^= rs << 13;
    rs ^= rs >> 17;
    rs ^= rs << 5;
    return rs;
}
static int rndint(int n) { return (int)(rnd32() % (uint32_t)n); }
static double rnd01(void) { return (double)(rnd32() >> 8) / 16777216.0; }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcd_ll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { long long t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* R[g*G + x] = x*g in the group with elements a*k+b, (a,b)(c,d) = (a + r^b c, b+d). */
static int *build_mul(int G, int m, int k, int r) {
    int *R = malloc(sizeof(int) * (size_t)G * (size_t)G);
    int *pw = malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    for (int x = 0; x < G; x++) {
        int a1 = x / k, b1 = x % k;
        for (int g = 0; g < G; g++) {
            int c = g / k, d2 = g % k;
            int A = (int)(((long long)a1 + (long long)pw[b1] * c) % m);
            int B = (b1 + d2) % k;
            R[g * G + x] = A * k + B;
        }
    }
    free(pw);
    return R;
}

static int list_specs(int G, Spec *out) {
    int n = 0;
    out[n].m = G; out[n].k = 1; out[n].r = 1; n++;
    for (int k = 2; k <= G && n < MAXSPEC; k++) {
        if (G % k) continue;
        int m = G / k;
        if (m < 2) continue;
        for (int r = 1; r < m && n < MAXSPEC; r++) {
            if (gcd_ll(r, m) != 1) continue;
            if (powmod_ll(r, k, m) != 1 % m) continue;
            out[n].m = m; out[n].k = k; out[n].r = r; n++;
        }
    }
    return n;
}

static int *g_nb = NULL;
static int *g_fill = NULL;
static int *g_seen = NULL;
static int *g_q = NULL;
static int g_stamp = 0;
static int g_d = 0, g_D = 0;
static Spec g_specs[MAXSPEC];

/* Each vertex receives exactly d neighbour entries (duplicates allowed). */
static void build_adj(int a, int G, const int *dst, const int *gv, const int *R, int *nb, int *fill) {
    int d = g_d;
    int N = 2 * a * G;
    for (int v = 0; v < N; v++) fill[v] = 0;
    int K = a * d;
    int off = a * G;
    for (int k = 0; k < K; k++) {
        int i = k / d, j = dst[k], gg = gv[k];
        const int *Rg = R + (size_t)gg * G;
        for (int x = 0; x < G; x++) {
            int u = i * G + x;
            int v = off + j * G + Rg[x];
            nb[u * d + fill[u]++] = v;
            nb[v * d + fill[v]++] = u;
        }
    }
}

static long long lift_cost(int a, int G) {
    int d = g_d, D = g_D;
    int N = 2 * a * G;
    long long total = 0;
    for (int s = 0; s < 2 * a; s++) {
        int src = (s < a) ? s * G : a * G + (s - a) * G;
        g_stamp++;
        int head = 0, tail = 0;
        g_seen[src] = g_stamp;
        g_q[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = g_q[head++];
                const int *p = g_nb + (size_t)u * d;
                for (int t = 0; t < d; t++) {
                    int v = p[t];
                    if (g_seen[v] != g_stamp) {
                        g_seen[v] = g_stamp;
                        g_q[tail++] = v;
                    }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static long long eval_run(const Run *r, const int *R) {
    build_adj(r->a, r->G, r->dst, r->gv, R, g_nb, g_fill);
    return lift_cost(r->a, r->G);
}

/* Returns 1 if solved (cost 0), 0 if the time slice ended first. */
static int anneal(Run *run, double slice_end, const int *R) {
    int K = run->a * g_d;
    if (run->cur < 0) run->cur = eval_run(run, R);
    while (run->cur > 0) {
        if (now() > slice_end) return 0;
        int odst[MAXK], ogv[MAXK];
        memcpy(odst, run->dst, sizeof(int) * K);
        memcpy(ogv, run->gv, sizeof(int) * K);
        if (rnd01() < 0.7) {
            int k = rndint(K);
            run->gv[k] = rndint(run->G);
        } else {
            int k1 = rndint(K), k2 = rndint(K);
            int t = run->dst[k1];
            run->dst[k1] = run->dst[k2];
            run->dst[k2] = t;
        }
        long long nc = eval_run(run, R);
        double dc = (double)(nc - run->cur);
        if (dc <= 0 || rnd01() < exp(-dc / run->T)) {
            run->cur = nc;
        } else {
            memcpy(run->dst, odst, sizeof(int) * K);
            memcpy(run->gv, ogv, sizeof(int) * K);
        }
        run->T *= 0.9995;
        if (run->T < 0.05) run->T = 0.05;
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: prog d D seed budget best_n moore\n");
        return 1;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long seed = strtoul(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long long bo = atoll(argv[5]);
    long long moore = atoll(argv[6]);

    rs = (uint32_t)(seed * 2654435761u + 12345u);
    if (rs == 0) rs = 1;
    double deadline = now() + budget;

    if (d < 2 || d > MAXD || D < 2 || moore < 4) {
        printf("0 0\n");
        return 0;
    }
    long long ncap = moore < NCAP_MAX ? moore : NCAP_MAX;
    g_d = d;
    g_D = D;
    g_nb = malloc(sizeof(int) * (size_t)ncap * (size_t)d);
    g_fill = malloc(sizeof(int) * (size_t)ncap);
    g_seen = calloc((size_t)ncap, sizeof(int));
    g_q = malloc(sizeof(int) * (size_t)ncap);

    Run best;
    memset(&best, 0, sizeof best);
    int have_best = 0;
    Run park[MAXPARK];
    int npark = 0;

    while (now() < deadline) {
        /* drop parked runs that can no longer beat the best order */
        int w = 0;
        for (int i = 0; i < npark; i++) {
            long long N = 2LL * park[i].a * park[i].G;
            if (N > bo && N <= ncap) park[w++] = park[i];
        }
        npark = w;

        Run tmp;
        memset(&tmp, 0, sizeof tmp);
        if (npark > 0 && rnd01() < 0.6) {
            int i = rndint(npark);
            tmp = park[i];
            park[i] = park[--npark];
        } else {
            int avail[MAXA], na = 0;
            for (int a = 1; a <= MAXA; a++) {
                long long hi = ncap / (2 * a);
                long long h2 = moore / (2 * a);
                if (h2 < hi) hi = h2;
                long long lo = bo / (2 * a) + 1;
                if (lo <= hi) avail[na++] = a;
            }
            if (na == 0) break;
            int a = avail[rndint(na)];
            long long lo = bo / (2 * a) + 1;
            long long hi = ncap / (2 * a);
            long long h2 = moore / (2 * a);
            if (h2 < hi) hi = h2;
            long long span = hi - lo + 1;
            if (span > 60) span = 60;
            int G = (int)(lo + rndint((int)span));
            int ns = list_specs(G, g_specs);
            Spec sp = g_specs[rndint(ns)];
            tmp.a = a;
            tmp.G = G;
            tmp.m = sp.m;
            tmp.k = sp.k;
            tmp.r = sp.r;
            tmp.T = 0.6;
            tmp.cur = -1;
            int K = a * d;
            for (int k = 0; k < K; k++) tmp.dst[k] = k / d;
            for (int k = K - 1; k > 0; k--) {
                int j = rndint(k + 1);
                int t = tmp.dst[k];
                tmp.dst[k] = tmp.dst[j];
                tmp.dst[j] = t;
            }
            for (int k = 0; k < K; k++) tmp.gv[k] = rndint(G);
        }

        double slice_end = now() + 2.5;
        if (slice_end > deadline) slice_end = deadline;
        int *R = build_mul(tmp.G, tmp.m, tmp.k, tmp.r);
        int solved = anneal(&tmp, slice_end, R);
        free(R);
        if (solved) {
            long long N = 2LL * tmp.a * tmp.G;
            if (N > bo) {
                bo = N;
                best = tmp;
                have_best = 1;
            }
        } else {
            if (npark < MAXPARK) park[npark++] = tmp;
            else park[rndint(MAXPARK)] = tmp;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    {
        int a = best.a, G = best.G, K = a * d;
        long long N = 2LL * a * G;
        int *R = build_mul(G, best.m, best.k, best.r);
        unsigned char *mark = calloc((size_t)N * (size_t)N, 1);
        int *eu = malloc(sizeof(int) * (size_t)K * (size_t)G);
        int *ev = malloc(sizeof(int) * (size_t)K * (size_t)G);
        long long m = 0;
        for (int k = 0; k < K; k++) {
            int i = k / d, j = best.dst[k], gg = best.gv[k];
            for (int x = 0; x < G; x++) {
                long long u = (long long)i * G + x;
                long long v = (long long)a * G + (long long)j * G + R[gg * G + x];
                if (!mark[u * N + v]) {
                    mark[u * N + v] = 1;
                    eu[m] = (int)u;
                    ev[m] = (int)v;
                    m++;
                }
            }
        }
        printf("%lld %lld\n", N, m);
        for (long long t = 0; t < m; t++) printf("%d %d\n", eu[t], ev[t]);
        free(R);
        free(mark);
        free(eu);
        free(ev);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured bases.
# ----------------------------------------------------------------------------

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
    """Generalized quadrangle incidence graph W(q) for the largest prime power q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Shared graph helpers.
# ----------------------------------------------------------------------------

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
    """Two-colouring of a bipartite graph given by adjacency lists or sets."""
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


def _cost(adj, D):
    """Number of vertex pairs at distance more than D (unreachable pairs count)."""
    n = len(adj)
    ball = _balls_radius(n, adj, D)
    return sum(n - b.bit_count() for b in ball) // 2


def _greedy_cover(cands, ball, full, d, rng, randomize):
    """Greedy set cover of `full` by at most d candidate vertices. Returns list or None."""
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
            for attempt in range(200):
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


# ----------------------------------------------------------------------------
# Twin duplication and randomized pipelines.
# ----------------------------------------------------------------------------

def _duplicate_twins(n, edges, d, rng):
    """Greedily add non-adjacent twins in random order while neighbours have spare degree."""
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
    """One randomized pipeline: mix twin duplication with cover growth and saturation."""
    mode = rng.randrange(3)
    n, e = base_n, list(base_e)
    if mode == 0:
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    elif mode == 1:
        n, e = _grow(n, e, d, D, deadline, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    else:
        e = _saturate_edges(n, e, d, rng)
        n, e = _duplicate_twins(n, e, d, rng)
        e = _saturate_edges(n, e, d, rng)
        n, e = _grow(n, e, d, D, deadline, rng)
    return n, e


# ----------------------------------------------------------------------------
# Python fallback for lifts, used only if the C engine cannot be compiled or run.
# ----------------------------------------------------------------------------

def _py_lift_fallback(d, D, get_best, rng, deadline, consider):
    moore = lib.moore_bound(d, D)
    while time.monotonic() < deadline:
        best = get_best()
        a = rng.choice((1, 2, 3))
        lo = best // (2 * a) + 1
        hi = min(moore // (2 * a), lo + 20)
        if lo > hi:
            continue
        G = rng.randint(lo, hi)
        opts = [(G, 1, 1)]
        for k in range(2, G + 1):
            if G % k == 0 and G // k >= 2:
                m = G // k
                for r in range(1, m):
                    if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                        opts.append((m, k, r))
        m, k, r = rng.choice(opts)
        _, mul, _ = lib.semidirect_group(m, k, r)
        left = [i for i in range(a) for _ in range(d)]
        right = list(left)
        rng.shuffle(right)
        darts = [(left[t], a + right[t], rng.randrange(G)) for t in range(len(left))]
        n, e = lib.group_lift(2 * a, darts, G, mul)
        cur = _cost(_to_sets(n, e), D)
        steps = 0
        while cur > 0 and steps < 600 and time.monotonic() < deadline:
            steps += 1
            old = list(darts)
            t = rng.randrange(len(darts))
            if rng.random() < 0.7:
                i, j, _ = darts[t]
                darts[t] = (i, j, rng.randrange(G))
            else:
                t2 = rng.randrange(len(darts))
                darts[t] = (darts[t][0], darts[t2][1], darts[t][2])
                darts[t2] = (darts[t2][0], old[t][1], darts[t2][2])
            n2, e2 = lib.group_lift(2 * a, darts, G, mul)
            c2 = _cost(_to_sets(n2, e2), D)
            if c2 <= cur:
                cur = c2
                n, e = n2, e2
            else:
                darts = old
        if cur == 0:
            consider(n, e)


def _c_lifts(d, D, seed, budget, best_n, moore):
    """Run the C lift search. Returns (n, edges) of an improved lift, or None."""
    out = lib.run_c(C_SOURCE,
                    [d, D, int(seed) & 0x7FFFFFFF, f"{budget:.2f}", int(best_n), int(moore)],
                    timeout=budget + 10.0)
    n, e = lib.parse_graph_text(out)
    if n < 1 or not e:
        return None
    return n, e


# ----------------------------------------------------------------------------
# Large-neighbourhood search and pruning.
# ----------------------------------------------------------------------------

def _fill(adj, color, d, rng):
    """Add cross-side edges between deficient vertices (only helps the diameter)."""
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
    """Bipartite double-edge switches (degrees unchanged) minimising bad pairs. True if cost reaches 0."""
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
    """Kill-repair-regrow large-neighbourhood search from a valid graph, anchored to its best."""
    cur_n, cur_e = n, list(edges)
    best_n, best_e = n, list(edges)
    while time.monotonic() < deadline:
        k = rng.choice((1, 1, 2, 2, 3, 4))
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
        n4, e4 = _grow(m, e3, d, D, deadline, rng)
        consider(n4, e4)
        if n4 > best_n:
            best_n, best_e = n4, list(e4)
        if n4 >= cur_n - 1:
            cur_n, cur_e = n4, e4
        elif n4 < best_n - 3:
            cur_n, cur_e = best_n, list(best_e)


def _prune_redundant(n, edges, D, rng, deadline, max_tests):
    """Delete random redundant edges (keeping diameter <= D). Returns the pruned edge list."""
    adj = _to_sets(n, edges)
    cand = list(edges)
    rng.shuffle(cand)
    tests = 0
    for u, v in cand:
        if tests >= max_tests or time.monotonic() > deadline:
            break
        if v not in adj[u]:
            continue
        tests += 1
        adj[u].discard(v)
        adj[v].discard(u)
        if _cost(adj, D) != 0:
            adj[u].add(v)
            adj[v].add(u)
    return [(a, b) for a in range(n) for b in adj[a] if a < b]


def _prune_regrow(n, edges, d, D, deadline, rng, consider):
    """Repeatedly prune redundant edges, regrow with cover vertices, keep the best."""
    best_n, best_e = n, list(edges)
    cur_n, cur_e = n, list(edges)
    while time.monotonic() < deadline:
        pe = _prune_redundant(cur_n, cur_e, D, rng, deadline, 160)
        n2, e2 = _grow(cur_n, pe, d, D, deadline, rng)
        consider(n2, e2)
        if n2 > best_n:
            best_n, best_e = n2, list(e2)
        if n2 >= cur_n - 1:
            cur_n, cur_e = n2, list(e2)
        elif n2 < best_n - 2 or rng.random() < 0.3:
            cur_n, cur_e = best_n, list(best_e)


# ----------------------------------------------------------------------------
# Driver. Budget split (fractions of time_limit):
#   A  structured base (W(q) for D >= 4, PG(2,q) for D = 3), grown to 0.10
#   L  C voltage-lift search over small groups, then grow the best lift, to 0.55
#   T  randomized twin/grow pipelines from the base and from the best graph, to 0.66
#   C  LNS from the best valid graph, to 0.84
#   P  redundant-edge pruning and regrowth, to 0.93
# Every kept graph passes lib.is_valid. The K_{d,d} fallback is always valid.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    rng = random.Random(seed)

    def at(f):
        return start + f * time_limit

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    fallback = lib.haar_graph(d, range(d))
    best_n, best_e = fallback
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best_n, best_e
        if n > best_n and lib.is_valid(n, e, d, D):
            best_n, best_e = n, list(e)
            return True
        return False

    if best_n >= moore:
        return best_n, list(best_e)

    # Phase A: structured base, grown.
    base_n, base_e = best_n, list(best_e)
    if D >= 3:
        base = _best_gq(d) if D >= 4 else None
        if base is None:
            base = _best_pg(d)
        if base is not None:
            n0, e0 = base
            if lib.is_valid(n0, e0, d, D):
                consider(n0, e0)
                base_n, base_e = n0, list(e0)
                n1, e1 = _grow(n0, e0, d, D, at(0.10), rng)
                consider(n1, e1)

    # Phase L: C voltage-lift search (Python fallback if the C engine fails).
    lift_end = at(0.55)
    if D >= 2 and d <= 15 and time.monotonic() < lift_end - 0.5:
        budget = lift_end - time.monotonic()
        c_ok = True
        res = None
        try:
            res = _c_lifts(d, D, seed, budget, best_n, moore)
        except Exception:
            c_ok = False
        if c_ok:
            if res is not None:
                n, e = res
                consider(n, e)
                n2, e2 = _grow(n, _saturate_edges(n, e, d, rng), d, D, at(0.62), rng)
                consider(n2, e2)
        else:
            _py_lift_fallback(d, D, lambda: best_n, rng, lift_end, consider)

    if best_n >= moore:
        return best_n, list(best_e)

    # Phase T: randomized pipelines from the structured base and from the best graph.
    trial_end = at(0.66)
    while time.monotonic() < trial_end:
        if rng.random() < 0.5:
            bn, be = base_n, base_e
        else:
            bn, be = best_n, best_e
        n, e = _trial(bn, be, d, D, rng, trial_end)
        consider(n, e)

    # Phase C: LNS from the best valid graph.
    lns_end = at(0.84)
    if time.monotonic() < lns_end:
        _lns(best_n, best_e, d, D, lns_end, rng, consider)

    # Phase P: prune redundant edges and regrow from the best graph.
    prune_end = at(0.93)
    if time.monotonic() < prune_end:
        _prune_regrow(best_n, best_e, d, D, prune_end, rng, consider)

    if not lib.is_valid(best_n, best_e, d, D):
        return fallback
    return best_n, list(best_e)
