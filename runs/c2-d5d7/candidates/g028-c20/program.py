"""Multi-fibre voltage-lift search for the d=5, D=7 target, with a safe algebraic fallback.

The parent used one-fibre bi-Cayley lifts (a single vertex fibre per side). This version
generalises the lift to a base multigraph with p fibres per side (p = 1..4). Each base is a
random connected d-regular bipartite multigraph on p+p fibres, and every dart (i, j) carries a
voltage g in a finite group G = Z_m x| Z_k of order N. The lift has 2pN vertices, is bipartite,
and has degree d. Because left multiplication by G is an automorphism that is transitive on
each fibre, diameter <= D holds exactly when a BFS from one vertex per fibre (2p BFS runs)
reaches everything within D. The annealer works directly on this orbit objective, with
the voltages on the dart list, and never builds the full graph during the search.

Parallel darts between the same fibre pair get distinct voltages, so the lift is simple.
Every candidate is verified in C by a full bitset diameter check, then again in Python with
lib.is_valid. The hexagon, generalised quadrangle, and projective-plane starts remain as
fallbacks, so every case still returns a valid graph.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre voltage lift search.
 * Usage: prog d D seed time_limit [min_n]
 * Output: "n m" and m edges of the largest valid lift found with n > min_n, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXH 2048
#define MAXP 4
#define MAXT (MAXP * MAXD)
#define SPAN 300
#define STEPS 4000
#define ATTEMPTS 3

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
} Graph;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered vertex pairs at distance > D (bitset BFS). */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int i = 0; i < g->deg[v]; i++) {
                const uint64_t *s = cur + (size_t)g->adj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long total = 0;
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        total += n - c;
    }
    return total / 2;
}

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

/* ---------------- groups ---------------- */

typedef struct { int m, k, r; int rp[MAXH]; } Grp;

static int MTAB[MAXH * MAXH];
static int INVT[MAXH];
static int NN;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible Z_m x| Z_k of order N (reservoir sampling). */
static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { G->m = m; G->k = k; G->r = r; }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

/* Prefer a non-abelian choice when one is sampled quickly. */
static int pick_group(int N, Grp *G) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

static void setup_group(int N, const Grp *G) {
    NN = N;
    for (int x = 0; x < N; x++) {
        int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++) row[y] = gmul(G, x, y);
    }
    for (int x = 0; x < N; x++) {
        const int *row = MTAB + (size_t)x * N;
        for (int y = 0; y < N; y++)
            if (row[y] == 0) { INVT[x] = y; break; }
    }
}

/* ---------------- base multigraph and darts ---------------- */

static int nd;
static int di[MAXT], dj[MAXT], dg[MAXT], dgi[MAXT];
static int outd[MAXP][MAXD], ind[MAXP][MAXD];

/* Random connected d-regular bipartite multigraph on p + p fibres. */
static void make_base(int p) {
    int M[MAXP][MAXP];
    for (;;) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * p) break;
    }
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                di[nd] = i; dj[nd] = j; dg[nd] = -1; nd++;
            }
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        outd[di[t]][ca[di[t]]++] = t;
        ind[dj[t]][cb[dj[t]]++] = t;
    }
}

/* Random voltage for dart t, distinct from other darts on the same fibre pair. */
static int pick_volt(int t, int N) {
    for (;;) {
        int g = rndint(N), ok = 1;
        for (int s = 0; s < nd && ok; s++)
            if (s != t && dg[s] == g && di[s] == di[t] && dj[s] == dj[t]) ok = 0;
        if (ok) return g;
    }
}

/* Orbit objective: unreached (source, vertex) pairs from one source per fibre.
 * Vertex id: A-fibre i element x -> i*N + x; B-fibre j element y -> (p+j)*N + y.
 * Edges: A(i,x) -- B(j, x*g) for each dart (i,j,g). */
static int vis[MAXN], vdist[MAXN], vq[MAXN];
static int vstamp = 0;

static long orbit_bad(int p, int N) {
    int V = 2 * p * N;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        int head = 0, tail = 0;
        vstamp++;
        vis[src] = vstamp;
        vdist[src] = 0;
        vq[tail++] = src;
        while (head < tail) {
            int v = vq[head++];
            int dv = vdist[v];
            if (dv >= D) continue;
            if (v < p * N) {
                int i = v / N, x = v - i * N;
                const int *row = MTAB + (size_t)x * N;
                for (int k = 0; k < d; k++) {
                    int t = outd[i][k];
                    int u = (p + dj[t]) * N + row[dg[t]];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        vdist[u] = dv + 1;
                        vq[tail++] = u;
                    }
                }
            } else {
                int j = v / N - p, y = v - (p + j) * N;
                const int *row = MTAB + (size_t)y * N;
                for (int k = 0; k < d; k++) {
                    int t = ind[j][k];
                    int u = di[t] * N + row[dgi[t]];
                    if (vis[u] != vstamp) {
                        vis[u] = vstamp;
                        vdist[u] = dv + 1;
                        vq[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

/* Annealed voltage search with geometric cooling 1.5 -> 0.15 over STEPS moves. */
static long climb(int p, int N, double until) {
    long bad = orbit_bad(p, N);
    double T = 1.5;
    const double alpha = pow(0.1, 1.0 / STEPS);
    for (long s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dg[t];
        int g = pick_volt(t, N);
        dg[t] = g;
        dgi[t] = INVT[g];
        long nb = orbit_bad(p, N);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            dg[t] = old;
            dgi[t] = INVT[old];
        }
        T *= alpha;
        if (T < 0.15) T = 0.15;
    }
    return bad;
}

/* ---------------- verification and output ---------------- */

static Graph gbuf;

static int full_check(int p, int N) {
    int n = 2 * p * N;
    if (n > MAXN) return 0;
    gbuf.n = n;
    for (int v = 0; v < n; v++) gbuf.deg[v] = 0;
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int A = di[t] * N + x;
            int B = (p + dj[t]) * N + MTAB[(size_t)x * N + dg[t]];
            if (gbuf.deg[A] >= d || gbuf.deg[B] >= d) return 0;
            add_edge(&gbuf, A, B);
        }
    for (int v = 0; v < n; v++)
        for (int i = 0; i < gbuf.deg[v]; i++)
            for (int j = 0; j < i; j++)
                if (gbuf.adj[v][i] == gbuf.adj[v][j]) return 0;
    return bad_pairs(&gbuf) == 0;
}

static int found = 0;
static long best_n = 0;
static int bp, bN, bnd;
static int bdi[MAXT], bdj[MAXT], bdg[MAXT];
static Grp bG;

static void record(int p, int N, const Grp *G) {
    bp = p;
    bN = N;
    bnd = nd;
    for (int t = 0; t < nd; t++) { bdi[t] = di[t]; bdj[t] = dj[t]; bdg[t] = dg[t]; }
    bG = *G;
    best_n = 2L * p * N;
    found = 1;
}

static void print_best(void) {
    if (!found) { printf("0 0\n"); return; }
    setup_group(bN, &bG);
    long m = (long)bnd * bN;
    printf("%ld %ld\n", 2L * bp * bN, m);
    for (int t = 0; t < bnd; t++)
        for (int x = 0; x < bN; x++) {
            int A = bdi[t] * bN + x;
            int B = (bp + bdj[t]) * bN + MTAB[(size_t)x * bN + bdg[t]];
            printf("%d %d\n", A, B);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [min_n]\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long minn = argc > 5 ? atol(argv[5]) : 0;
    double t0 = now();
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD - 1 || D < 1) { printf("0 0\n"); return 0; }
    best_n = minn;
    long moore = moore_bound();
    static Grp G;

    while (now() < t_end) {
        if (best_n >= moore || best_n >= MAXN) break;
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long lo = best_n / (2 * p) + 1;
        if (lo < d + 1) lo = d + 1;
        long hi = moore / (2 * p);
        if (hi > MAXH) hi = MAXH;
        if (hi > MAXN / (2 * p)) hi = MAXN / (2 * p);
        if (lo > hi) continue;
        long span = hi - lo + 1;
        if (span > SPAN) span = SPAN;
        double u = rnd01();
        long N = lo + (long)(u * sqrt(u) * span);
        if (N > hi) N = hi;
        if (!pick_group((int)N, &G)) continue;
        setup_group((int)N, &G);
        for (int att = 0; att < ATTEMPTS && now() < t_end; att++) {
            make_base(p);
            for (int t = 0; t < nd; t++) {
                dg[t] = pick_volt(t, (int)N);
                dgi[t] = INVT[dg[t]];
            }
            long b = climb(p, (int)N, t_end);
            if (b == 0 && 2L * p * N > best_n && full_check(p, (int)N)) {
                record(p, (int)N, &G);
                break;
            }
        }
    }
    print_best();
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 15 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, best[0]],
                         stdin_graph=None, timeout=budget + 5)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
