import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

/* Voltage-lift annealing over semidirect products Z_m x| Z_k2.
   Base: K vertices per side, DEG random perfect matchings (DEG-regular).
   Lift: vertex (u, x) for u < 2K, x in group of order NO. Dart (u,v,g) gives
   edges (u,x)-(v, x*g). Cost = number of unordered vertex pairs at distance > DIAM.
   Output: best zero-cost lift found (bipartite, max degree DEG, diameter <= DIAM). */

#define KMAX 4
#define MAXDEG 64
#define NCAP 6000
#define ITERS 4000

static int DEG, DIAM, K, NO, NDART;
static int du[KMAX * MAXDEG], dv[KMAX * MAXDEG], dg[KMAX * MAXDEG];
static int adj[NCAP * MAXDEG];
static int deg[NCAP];
static uint64_t *R1, *R2;
static int *best_e;
static int best_n = 0, best_m = 0;
static uint64_t rs;

static uint64_t rnext(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd(int n) { return (int)(rnext() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnext() >> 11) / 9007199254740992.0; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

typedef struct { int G, m, k2; long long powr[16]; } Grp;

/* Element x = a*k2 + b codes (a,b) in Z_m x| Z_k2; (a,b)*(c,d) = (a + r^b c, b + d). */
static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2;
    int c = y / g->k2, d = y % g->k2;
    int aa = (int)((a + g->powr[b] * c) % g->m);
    int bb = (b + d) % g->k2;
    return aa * g->k2 + bb;
}

static int sample_group(Grp *g, int G) {
    int cand[64], nc = 0;
    for (int k2 = 1; k2 <= 12; k2++)
        if (G % k2 == 0 && G / k2 >= 2) cand[nc++] = k2;
    if (nc == 0) return 0;
    int k2 = cand[rnd(nc)];
    int m = G / k2;
    long long r = 1;
    if (k2 > 1) {
        int ok = 0;
        for (int t = 0; t < 200 && !ok; t++) {
            long long rr = 1 + rnd(m - 1);
            if (gcd_i((int)rr, m) == 1 && powmod_ll(rr, k2, m) == 1 % m) {
                r = rr; ok = 1;
            }
        }
        if (!ok) { k2 = 1; m = G; r = 1; }
    }
    g->G = G; g->m = m; g->k2 = k2;
    g->powr[0] = 1 % m;
    for (int b = 1; b < 16; b++) g->powr[b] = g->powr[b - 1] * r % m;
    return 1;
}

static void sample_base(void) {
    int idx = 0;
    for (int p = 0; p < DEG; p++) {
        int perm[KMAX];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            du[idx] = i;
            dv[idx] = K + perm[i];
            idx++;
        }
    }
    NDART = idx;
}

static void build_adj(const Grp *g) {
    int nv = 2 * K * NO;
    memset(deg, 0, sizeof(int) * nv);
    for (int j = 0; j < NDART; j++) {
        for (int x = 0; x < NO; x++) {
            int a = du[j] * NO + x;
            int b = dv[j] * NO + gmul(g, x, dg[j]);
            int dup = 0;
            for (int t = 0; t < deg[a]; t++)
                if (adj[a * MAXDEG + t] == b) { dup = 1; break; }
            if (!dup) {
                adj[a * MAXDEG + deg[a]++] = b;
                adj[b * MAXDEG + deg[b]++] = a;
            }
        }
    }
}

static long long cost(void) {
    int nv = 2 * K * NO;
    int Wc = (nv + 63) / 64;
    uint64_t *A = R1, *B = R2;
    memset(A, 0, sizeof(uint64_t) * (size_t)nv * Wc);
    for (int v = 0; v < nv; v++)
        A[(size_t)v * Wc + v / 64] |= 1ULL << (v % 64);
    for (int s = 0; s < DIAM; s++) {
        for (int v = 0; v < nv; v++) {
            uint64_t *out = B + (size_t)v * Wc;
            memcpy(out, A + (size_t)v * Wc, sizeof(uint64_t) * Wc);
            for (int t = 0; t < deg[v]; t++) {
                const uint64_t *in = A + (size_t)adj[v * MAXDEG + t] * Wc;
                for (int w = 0; w < Wc; w++) out[w] |= in[w];
            }
        }
        uint64_t *tmp = A; A = B; B = tmp;
    }
    long long unreached = 0;
    for (int v = 0; v < nv; v++) {
        int c = 0;
        for (int w = 0; w < Wc; w++) c += popc(A[(size_t)v * Wc + w]);
        unreached += nv - c;
    }
    return unreached / 2;
}

static void save_best(void) {
    int nv = 2 * K * NO;
    if (nv <= best_n) return;
    int m = 0;
    for (int a = 0; a < nv; a++)
        for (int t = 0; t < deg[a]; t++) {
            int b = adj[a * MAXDEG + t];
            if (b > a) {
                best_e[2 * m] = a;
                best_e[2 * m + 1] = b;
                m++;
            }
        }
    best_n = nv;
    best_m = m;
}

static double moore_c(int d, int D) {
    if (D == 0 || d == 0) return 1;
    if (d == 1) return D >= 1 ? 2 : 1;
    if (d == 2) return 2.0 * D;
    double s = 0, p = 1;
    for (int i = 0; i < D; i++) { s += p; p *= (d - 1); }
    return 2 * s;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    DEG = d; DIAM = D;
    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 88172645463325252ULL;

    R1 = malloc(sizeof(uint64_t) * (size_t)NCAP * ((NCAP + 63) / 64));
    R2 = malloc(sizeof(uint64_t) * (size_t)NCAP * ((NCAP + 63) / 64));
    best_e = malloc(sizeof(int) * (size_t)NCAP * MAXDEG);
    if (!R1 || !R2 || !best_e) return 1;

    if (d < 3 || d > MAXDEG || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double mooreb = moore_c(d, D);
    int nmax = mooreb < NCAP ? (int)mooreb : NCAP;
    double limit = budget * 0.9 - 0.3;
    clock_t t0 = clock();

    while (1) {
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el >= limit) break;

        int k = 1 + rnd(KMAX);
        int G = best_n / (2 * k) + 1 + rnd(3);
        if (G < 2) G = 2;
        if (2 * k * G > nmax) G = nmax / (2 * k);
        if (G < 2) {
            k = 1;
            G = nmax / 2;
            if (G < 2) break;
        }

        Grp g;
        if (!sample_group(&g, G)) continue;
        K = k;
        NO = G;
        sample_base();
        for (int j = 0; j < NDART; j++) dg[j] = rnd(NO);
        build_adj(&g);
        long long c = cost();

        for (int it = 0; it < ITERS && c > 0; it++) {
            if ((it & 127) == 0) {
                double e2 = (double)(clock() - t0) / CLOCKS_PER_SEC;
                if (e2 >= limit) break;
            }
            int j = rnd(NDART);
            int old = dg[j];
            int nvv = rnd(NO - 1);
            if (nvv >= old) nvv++;
            dg[j] = nvv;
            build_adj(&g);
            long long c2 = cost();
            double T = 1.5 * (1.0 - (double)it / ITERS) + 0.05;
            if (c2 <= c || rdbl() < exp(-(double)(c2 - c) / T)) {
                c = c2;
            } else {
                dg[j] = old;
                build_adj(&g);
            }
        }
        if (c == 0) save_best();
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++)
        printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    return 0;
}
"""


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
    """W(q) incidence graph for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if q <= 16 and lib.is_prime_power(q):
            return _gq_w(q)
    return None


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
    """Greedily add vertices whose neighbourhoods cover all vertices within distance D-1."""
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
    """Greedily join deficient opposite-side vertices in random order."""
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
    """Extend by cover vertices first, then saturate edges with the remaining spare degree."""
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


def build(d, D, seed, time_limit):
    start = time.monotonic()
    end = start + 0.85 * time_limit - 2.0
    base_end = start + 0.35 * time_limit
    rng = random.Random(seed)

    if D == 1 and d >= 1:
        return 2, [(0, 1)]
    if d < 1 or D < 1:
        return 1, []

    # Safe fallback: K_{d,d}, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    moore = lib.moore_bound(d, D)

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Phase A: classical bases (projective plane / W(q)) grown by cover extension.
    if D >= 3 and best_n < moore:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if best_n < moore:
                n2, e2 = _grow(pg[0], pg[1], d, D, base_end, rng)
                consider(n2, e2)

    if D >= 4 and best_n < moore:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            attempts = 0
            while time.monotonic() < base_end and attempts < 30 and best_n < moore:
                attempts += 1
                sub = random.Random(rng.randrange(1 << 30))
                src = gq if (attempts % 2 == 1 or best_n <= gq[0]) else best
                n2, e2 = _grow(src[0], src[1], d, D, base_end, sub)
                consider(n2, e2)

    # Phase B: C annealing over voltage lifts on semidirect product groups.
    if best_n < moore and d >= 3 and D >= 2:
        budget = end - time.monotonic()
        if budget > 3.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                                stdin_graph=None, timeout=budget + 5.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
