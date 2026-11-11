"""Bipartite degree-diameter search.

Exact constructions (projective planes, Araujo-Pardo--Lopez, generalized quadrangles)
handle the small cases. Otherwise a C engine searches bi-Cayley lifts over semidirect
products Z_m x| Z_c with k base vertices per side. Diameter is checked at base level with
group-valued reach sets, which is much cheaper than a full-graph BFS. Each success is
re-checked on the full graph in C, and the Python driver validates again before use.
"""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# C engine: group-lift search with base-level reach sets.
#
# Lift: base has K A-vertices and K B-vertices. Layer l pairs A_i with
# B_{sig[l][i]} with voltage vol[l][i] in G = Z_m x| Z_c. The lift has 2KN vertices,
# A(i,x) = i*N + x and B(j,y) = K*N + j*N + y, with A(i,x) ~ B(j, x*s).
# Reach sets are subsets of G per base vertex, updated by right multiplication.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 2816
#define MAXK 4
#define MAXD 32
#define MAXV (2 * MAXK)
#define MAXN 16384
#define MAXE 300000
#define MAXCAND 4096
#define SLICE 3.0

static int d, D;
static double t_end;
static long moore;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcdi(int a, int b) {
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

/* ---------------- group Z_m x| Z_c, element a*c+b ---------------- */
static int G_N, G_m, G_c, G_r;
static int rp[MAXG];
static uint16_t mt[MAXG * MAXG];
static int inv_[MAXG];

static int mulg(int x, int y) {
    int a = x / G_c, b = x % G_c, c = y / G_c, e = y % G_c;
    return (int)(((long)a + (long)rp[b] * c) % G_m) * G_c + (b + e) % G_c;
}

static void build_group(int m, int c, int r) {
    G_m = m; G_c = c; G_r = r; G_N = m * c;
    rp[0] = 1 % m;
    for (int b = 1; b < c; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    int N = G_N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) mt[x * N + y] = (uint16_t)mulg(x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (mt[x * N + y] == 0) inv_[x] = y;
}

typedef struct { int m, c, r; } GCand;
static GCand cands[MAXCAND];
static int ncand;

static void list_groups(int N) {
    ncand = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int c = N / m;
        if (m == 1) {
            if (ncand < MAXCAND) { cands[ncand].m = 1; cands[ncand].c = c; cands[ncand].r = 0; ncand++; }
            continue;
        }
        for (int r = 1; r < m && ncand < MAXCAND; r++) {
            if (gcdi(r, m) != 1) continue;
            if (powmod(r, c, m) != 1 % m) continue;
            cands[ncand].m = m; cands[ncand].c = c; cands[ncand].r = r;
            ncand++;
        }
    }
}

/* ---------------- lift configuration ---------------- */
static int K;
static int sig[MAXD][MAXK];
static int vol[MAXD][MAXK];
static int outn[MAXV], outw[MAXV][MAXD], outh[MAXV][MAXD];

static void build_out(void) {
    int V = 2 * K;
    for (int v = 0; v < V; v++) outn[v] = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) {
            int j = sig[l][i], s = vol[l][i];
            outw[i][outn[i]] = K + j;
            outh[i][outn[i]++] = s;
            outw[K + j][outn[K + j]] = i;
            outh[K + j][outn[K + j]++] = inv_[s];
        }
}

static unsigned char bufA[MAXV * MAXG], bufB[MAXV * MAXG];

/* Total number of (source base vertex, base vertex, group element) triples at distance > D. */
static long eval_unc(void) {
    int V = 2 * K, N = G_N;
    long unc = 0;
    build_out();
    for (int s0 = 0; s0 < V; s0++) {
        unsigned char *cur = bufA, *nxt = bufB;
        memset(cur, 0, (size_t)V * N);
        cur[(size_t)s0 * N] = 1;
        for (int r = 0; r < D; r++) {
            memcpy(nxt, cur, (size_t)V * N);
            int changed = 0;
            for (int v = 0; v < V; v++) {
                unsigned char *dst = nxt + (size_t)v * N;
                for (int t = 0; t < outn[v]; t++) {
                    const unsigned char *src = cur + (size_t)outw[v][t] * N;
                    int hi = inv_[outh[v][t]];
                    for (int y = 0; y < N; y++) {
                        if (src[y]) {
                            int z = mt[y * N + hi];
                            if (!dst[z]) { dst[z] = 1; changed = 1; }
                        }
                    }
                }
            }
            unsigned char *tmp = cur; cur = nxt; nxt = tmp;
            if (!changed) break;
        }
        for (int i = 0; i < V * N; i++)
            if (!cur[i]) unc++;
    }
    return unc;
}

/* Number of repeated (i, sig, vol) triples; each one is a parallel edge. */
static long dup_count(void) {
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = 0; l2 < l; l2++)
                if (sig[l][i] == sig[l2][i] && vol[l][i] == vol[l2][i]) dup++;
    return dup;
}

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) sig[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = sig[l][i]; sig[l][i] = sig[l][j]; sig[l][j] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rndint(G_N);
    }
}

static long PEN;

/* Simulated annealing on the current group. Returns 1 when base-level diameter holds. */
static int attempt(double until) {
    random_config();
    long cost = eval_unc() + PEN * dup_count();
    double start = now();
    double span = until - start;
    if (span <= 1e-3) span = 1e-3;
    double T = 1.0;
    long it = 0;
    while (cost > 0) {
        if ((it & 15) == 0) {
            double tn = now();
            if (tn >= until) break;
            double frac = (tn - start) / span;
            T = 3.0 * pow(0.03 / 3.0, frac);
        }
        it++;
        int l = rndint(d), i = rndint(K);
        int swapmove = (K >= 2 && rndint(8) == 0);
        int i2 = 0, old_v = 0;
        if (swapmove) {
            i2 = rndint(K);
            if (i2 == i) continue;
            int t = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = t;
        } else {
            old_v = vol[l][i];
            int nv = rndint(G_N);
            if (nv == old_v) continue;
            vol[l][i] = nv;
        }
        long nc = eval_unc() + PEN * dup_count();
        long dl = nc - cost;
        if (dl <= 0 || rnd01() < exp(-(double)dl / T)) {
            cost = nc;
        } else if (swapmove) {
            int t = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = t;
        } else {
            vol[l][i] = old_v;
        }
    }
    return cost == 0;
}

/* Edge list of the current lift. */
static int eu[MAXE], ev[MAXE];
static int bu[MAXE], bv[MAXE];
static int bne = 0;
static long best_n = 0;

static int lift_edges(void) {
    int N = G_N, ne = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++)
            for (int x = 0; x < N; x++) {
                int y = mt[x * N + vol[l][i]];
                eu[ne] = i * N + x;
                ev[ne] = K * N + sig[l][i] * N + y;
                ne++;
            }
    return ne;
}

/* Full-graph check: max degree d and every pair within distance D. */
static int full_ok(int n, int ne) {
    int W = (n + 63) / 64;
    int *deg = calloc((size_t)n, sizeof(int));
    int *adj = malloc(sizeof(int) * (size_t)n * d);
    uint64_t *cur = calloc((size_t)n * W, sizeof(uint64_t));
    uint64_t *nxt = malloc(sizeof(uint64_t) * (size_t)n * W);
    int ok = deg && adj && cur && nxt;
    if (ok) {
        for (int e = 0; e < ne && ok; e++) {
            int u = eu[e], v = ev[e];
            if (deg[u] >= d || deg[v] >= d) ok = 0;
            else {
                adj[u * d + deg[u]++] = v;
                adj[v * d + deg[v]++] = u;
            }
        }
    }
    if (ok) {
        for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
        for (int r = 0; r < D; r++) {
            for (int v = 0; v < n; v++) {
                uint64_t *dst = nxt + (size_t)v * W;
                memcpy(dst, cur + (size_t)v * W, sizeof(uint64_t) * W);
                for (int t = 0; t < deg[v]; t++) {
                    const uint64_t *src = cur + (size_t)adj[v * d + t] * W;
                    for (int w = 0; w < W; w++) dst[w] |= src[w];
                }
            }
            uint64_t *tmp = cur; cur = nxt; nxt = tmp;
        }
        for (int v = 0; v < n && ok; v++) {
            int c = 0;
            for (int w = 0; w < W; w++) c += __builtin_popcountll(cur[(size_t)v * W + w]);
            if (c != n) ok = 0;
        }
    }
    free(deg);
    free(adj);
    free(cur);
    free(nxt);
    return ok;
}

static void search(void) {
    while (now() < t_end) {
        if (best_n >= moore) break;
        int r = rndint(10);
        int k = r < 5 ? 1 : r < 8 ? 2 : r < 9 ? 3 : 4;
        long Nmin = best_n / (2L * k) + 1;
        if (Nmin < d) Nmin = d;
        if (2L * k * Nmin > moore || 2L * k * Nmin > MAXN || Nmin > MAXG - 1) continue;
        long N = Nmin + rndint((int)(1 + Nmin / 60));
        if (2L * k * N > moore || 2L * k * N > MAXN || N > MAXG - 1) N = Nmin;
        list_groups((int)N);
        if (ncand == 0) continue;
        GCand gc = cands[rndint(ncand)];
        build_group(gc.m, gc.c, gc.r);
        K = k;
        PEN = 4L * K * K * G_N + 10;
        double until = now() + SLICE;
        if (until > t_end) until = t_end;
        if (!attempt(until)) continue;
        int ne = lift_edges();
        int n = 2 * K * G_N;
        if (!full_ok(n, ne)) continue;
        if (n > best_n) {
            best_n = n;
            bne = ne;
            memcpy(bu, eu, sizeof(int) * ne);
            memcpy(bv, ev, sizeof(int) * ne);
        }
    }
}

static void print_edges(int n, int ne, const int *u, const int *v) {
    printf("%d %d\n", n, ne);
    for (int e = 0; e < ne; e++) printf("%d %d\n", u[e], v[e]);
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.92;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    moore = moore_bound();
    if (d >= 2 && D >= 2) search();

    if (bne == 0) {
        int ne = 0;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) {
                eu[ne] = a;
                ev[ne] = d + b;
                ne++;
            }
        print_edges(2 * d, ne, eu, ev);
    } else {
        print_edges((int)best_n, bne, bu, bv);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: group-lift annealing in C.
    if D >= 2:
        c_budget = end - time.monotonic() - 1.0
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 6)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
