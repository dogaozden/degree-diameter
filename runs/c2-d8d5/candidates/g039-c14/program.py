"""Bi-Cayley Haar-type lift search in C, seeded by exact constructions and a K_{d,d} fallback."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: bi-Cayley lifts over groups Z_m x| Z_k2 with K base vertices per side.
# Vertex (block b, group element g) with block b < K is A_b, otherwise B_{b-K}.
# Layer l pairs A_i with B_{PI[l][i]} through voltage SV[l][i]:
#   A_{i,g} ~ B_{PI[l][i], g*s}.
# Left translations are automorphisms, so distances from the 2K base vertices
# to everything decide the diameter. Simulated annealing on the voltages and
# permutations; the target order grows whenever a valid lift is found.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define MAXL 32
#define MAXG 2048
#define MAXE (1 << 18)
#define PEN 1000L
#define ITER 40000
#define PATIENCE 6000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Number of unordered vertex pairs at distance > D. */
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

static int is_valid_graph(const Graph *g) {
    if (g->n <= 0 || g->n > MAXN) return 0;
    for (int v = 0; v < g->n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= g->n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    return bad_pairs(g) == 0;
}

/* ---- groups: Z_m x|_r Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int GO;
static int RP[MAXG];
static unsigned short MT[MAXG * MAXG];
static int INVT[MAXG];
static int GA[MAXG], GB[MAXG];

static int random_group(int N, int *om, int *ok2, int *orr) {
    long count = 0;
    int found = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) {
                *om = m; *ok2 = k2; *orr = r;
                found = 1;
            }
        }
    }
    return found;
}

static void build_group(int m, int k2, int r, int g) {
    GO = g;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < g; x++) { GA[x] = x / k2; GB[x] = x % k2; }
    for (int x = 0; x < g; x++)
        for (int y = 0; y < g; y++) {
            long a = (GA[x] + (long)RP[GB[x]] * GA[y]) % m;
            int z = (int)(a * k2 + (GB[x] + GB[y]) % k2);
            MT[x * g + y] = (unsigned short)z;
            if (z == 0) INVT[x] = y;
        }
}

/* ---- bi-Cayley state ---- */
static int K;
static int PI[MAXL][MAXK], PINV[MAXL][MAXK], SV[MAXL][MAXK];
static int NB[MAXN * MAXL];
static unsigned char BUF0[MAXN], BUF1[MAXN];

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i]; p[i] = p[j]; p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            PI[l][i] = p[i];
            PINV[l][p[i]] = i;
        }
        for (int i = 0; i < K; i++) SV[l][i] = rndint(GO);
    }
}

static void swap_pi(int l, int b1, int b2) {
    int t = PI[l][b1]; PI[l][b1] = PI[l][b2]; PI[l][b2] = t;
    PINV[l][PI[l][b1]] = b1;
    PINV[l][PI[l][b2]] = b2;
}

/* Cost = (number of unreached (vertex, base representative) pairs) + penalty * duplicate darts. */
static long eval_cost(void) {
    int V = 2 * K * GO;
    for (int b = 0; b < K; b++)
        for (int g = 0; g < GO; g++) {
            int v = b * GO + g;
            for (int l = 0; l < d; l++) {
                int j = PI[l][b];
                NB[v * d + l] = (K + j) * GO + MT[g * GO + SV[l][b]];
            }
        }
    for (int j = 0; j < K; j++)
        for (int h = 0; h < GO; h++) {
            int v = (K + j) * GO + h;
            for (int l = 0; l < d; l++) {
                int i = PINV[l][j];
                NB[v * d + l] = i * GO + MT[h * GO + INVT[SV[l][i]]];
            }
        }
    unsigned char *cur = BUF0, *nxt = BUF1;
    memset(cur, 0, (size_t)V);
    for (int b = 0; b < 2 * K; b++) cur[b * GO] = (unsigned char)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < V; v++) {
            unsigned x = cur[v];
            const int *nb = NB + v * d;
            for (int l = 0; l < d; l++) x |= cur[nb[l]];
            nxt[v] = (unsigned char)x;
            if (x != cur[v]) changed = 1;
        }
        unsigned char *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < V; v++) unreached += 2 * K - __builtin_popcount((unsigned)cur[v]);
    long dups = 0;
    for (int b = 0; b < K; b++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (PI[l][b] == PI[l2][b] && SV[l][b] == SV[l2][b]) dups++;
    return unreached + PEN * dups;
}

static int sa_attempt(void) {
    random_state();
    long cost = eval_cost();
    long bestc = cost, last = 0;
    for (long it = 0; it < ITER; it++) {
        if (cost == 0) return 1;
        if ((it & 255) == 0 && now() > t_end) return 0;
        if (it - last > PATIENCE) return 0;
        double frac = (double)it / ITER;
        double T = 0.3 + 0.1 * (double)cost * (1.0 - frac);
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d), b1 = rndint(K), b2 = rndint(K - 1);
            if (b2 >= b1) b2++;
            swap_pi(l, b1, b2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else swap_pi(l, b1, b2);
        } else {
            int l = rndint(d), b = rndint(K);
            int old = SV[l][b], nw = rndint(GO);
            if (nw == old) continue;
            SV[l][b] = nw;
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else SV[l][b] = old;
        }
        if (cost < bestc) { bestc = cost; last = it; }
    }
    return cost == 0;
}

/* ---- best graph store ---- */
static int best_n, best_m;
static int BU[MAXE], BV[MAXE];
static int TU[MAXE], TV[MAXE];
static Graph vg;

static void record(void) {
    int V = 2 * K * GO;
    int m = 0;
    for (int i = 0; i < K; i++)
        for (int g = 0; g < GO; g++)
            for (int l = 0; l < d; l++) {
                if (m >= MAXE) return;
                TU[m] = i * GO + g;
                TV[m] = (K + PI[l][i]) * GO + MT[g * GO + SV[l][i]];
                m++;
            }
    vg.n = V;
    for (int v = 0; v < V; v++) {
        vg.deg[v] = 0;
        vg.side[v] = (unsigned char)(v >= K * GO);
    }
    for (int e = 0; e < m; e++) add_edge(&vg, TU[e], TV[e]);
    if (!is_valid_graph(&vg)) return;
    best_n = V;
    best_m = m;
    memcpy(BU, TU, sizeof(int) * (size_t)m);
    memcpy(BV, TV, sizeof(int) * (size_t)m);
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
    t_end = t0 + limit * 0.97 - 0.3;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    /* Safe fallback: K_{d,d}, diameter 2. */
    if (d < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    best_n = 2 * d;
    best_m = 0;
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) {
            BU[best_m] = a;
            BV[best_m] = d + b;
            best_m++;
        }
    if (d < 2 || D < 2) {
        printf("%d %d\n", best_n, best_m);
        for (int e = 0; e < best_m; e++) printf("%d %d\n", BU[e], BV[e]);
        return 0;
    }

    long moore = moore_bound();
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }

    while (now() < t_end) {
        int cand[MAXK], nc = 0;
        for (int k = 1; k <= MAXK; k++) {
            long lo = (long)best_n / (2 * k) + 1;
            if (2 * k * lo <= moore && 2 * k * lo <= MAXN && lo <= MAXG) cand[nc++] = k;
        }
        if (nc == 0) break;
        int k;
        if (rnd01() < 0.2) {
            k = cand[rndint(nc)];
        } else {
            double bs = -1e18;
            k = cand[0];
            for (int c = 0; c < nc; c++) {
                int kk = cand[c];
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = kk; }
            }
        }
        long lo = (long)best_n / (2 * k) + 1;
        long gl = lo + rndint(3);
        if (2 * k * gl > moore || 2 * k * gl > MAXN || gl > MAXG) gl = lo;
        int N = (int)gl;
        int m, k2, r;
        if (!random_group(N, &m, &k2, &r)) continue;
        K = k;
        build_group(m, k2, r, N);
        trials[k]++;
        if (sa_attempt()) {
            long before = best_n;
            record();
            if (best_n > before) wins[k]++;
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", BU[e], BV[e]);
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
        """Replace best with (n, e) if it is larger and valid."""
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

    # Bi-Cayley lift search in C.
    if 2 <= d <= 32 and D >= 2:
        budget = end - time.monotonic() - 1.0
        if budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                                 stdin_graph=None, timeout=budget + 10.0)
                n, e = lib.parse_graph_text(text)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
