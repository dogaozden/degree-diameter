"""Combined program, v3 (bold change for the weak d=3, D=9 case).

The parent searched voltage lifts over random groups and grew the result by two vertices at a time.
This version replaces that with a different algebraic search:

1. Exhaustive bi-Cayley search (d = 3 only). One vertex per side over a group G of order N,
   voltages {e, a, b}. Every semidirect group Z_m x| Z_k of order N is enumerated, and every
   voltage pair is tested by two BFS runs (from a_e and b_e). The first valid graph at each N is
   kept, and N increases, so the search climbs past the parent's N.
2. Random multi-fibre lifts (p = 1, 2, 3 vertices per fibre side) over the same semidirect groups.
   Voltages are improved by hill climbing on an orbit-reduced objective: BFS from the 2p fibre
   representatives, plus a penalty for parallel darts.

Python builds a valid algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez, or K_{d,d}) and
checks every result with lib.is_valid, so a valid fallback is always returned.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, v3.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Group: G = Z_m x|_r Z_k, element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k).
 * A multiplication table (MT) and inverse table (IV) are built per group.
 *
 * Lift: p fibres per side, each side acts by left multiplication of G on its elements.
 * Dart (i, j, g) joins A_i x to B_j (x*g). The lift is d-regular and bipartite. G acts
 * regularly on each fibre, so BFS from one representative per fibre checks all pairs.
 */
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
#define MAXG 512
#define MAXP 3
#define MAXDART (MAXD * MAXP)
#define MAXTRI 512

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
} Tri;

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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
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

static int is_valid(const Graph *g) {
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

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) { g->side[u] = 1 - g->side[v]; queue[tail++] = u; }
                else if (g->side[u] == g->side[v]) { g->n = 0; return; }
            }
        }
    }
    if (!is_valid(g)) g->n = 0;
}

static void print_graph(const Graph *g) {
    long m = 0;
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) m++;
    printf("%d %ld\n", g->n, m);
    for (int u = 0; u < g->n; u++)
        for (int i = 0; i < g->deg[u]; i++)
            if (u < g->adj[u][i]) printf("%d %d\n", u, g->adj[u][i]);
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------------------------------------------------------- groups */

static int MT[MAXG * MAXG];   /* product of x and y is MT[(x << 9) | y] */
static int IV[MAXG];          /* inverse of x */
static int rp_[MAXG];         /* r^b mod m */

static void build_group(int m, int k, int r) {
    int N = m * k;
    rp_[0] = 1 % m;
    for (int b = 1; b < k; b++) rp_[b] = (int)((long)rp_[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long aa = (a + (long)rp_[b] * c) % m;
            MT[((unsigned)x << 9) | (unsigned)y] = (int)(aa * k + (b + e) % k);
        }
    }
    for (int x = 0; x < N; x++) {
        IV[x] = 0;
        for (int y = 0; y < N; y++)
            if (MT[((unsigned)x << 9) | (unsigned)y] == 0) { IV[x] = y; break; }
    }
}

static Tri tris[MAXTRI];
static int ntri;

/* All semidirect groups Z_m x|_r Z_k of order N (cyclic when m = N or r = 1). */
static void list_groups(int N) {
    ntri = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (ntri < MAXTRI) {
                tris[ntri].m = m;
                tris[ntri].k = k;
                tris[ntri].r = r;
                ntri++;
            }
        }
    }
}

/* ------------------------------------------------- lifts (shared by all phases) */

static int P_, NN_, nd_;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];

/* A vertex of fibre i, element x -> i*N + x. B vertex of fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) gives edges A_i x ~ B_j (x*g) for all x. */
static void build_lift(Graph *g) {
    int p = P_, N = NN_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x,
                     p * N + dJ[t] * N + MT[((unsigned)x << 9) | (unsigned)dG[t]]);
}

static long dup_count(void) {
    long c = 0;
    for (int t = 0; t < nd_; t++)
        for (int s = 0; s < t; s++)
            if (dI[s] == dI[t] && dJ[s] == dJ[t] && dG[s] == dG[t]) c++;
    return c;
}

static int dist_b[MAXN], qu_b[MAXN];

/* Orbit-reduced objective: unreached pairs from the 2p fibre representatives. */
static long orbit_bad(const Graph *g) {
    int p = P_, N = NN_, nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_b[v] = -1;
        int head = 0, tail = 0;
        dist_b[src] = 0;
        qu_b[tail++] = src;
        while (head < tail) {
            int v = qu_b[head++];
            if (dist_b[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_b[u] < 0) {
                    dist_b[u] = dist_b[v] + 1;
                    qu_b[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

/* Random base: d permutations of p fibres, each giving p darts; random voltages. */
static void random_base(void) {
    int p = P_, N = NN_;
    nd_ = 0;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            dI[nd_] = i;
            dJ[nd_] = perm[i];
            dG[nd_] = rndint(N);
            nd_++;
        }
    }
}

/* Hill climbing on voltages; returns 0 iff the lift is valid up to the duplicate check. */
static long climb(Graph *g, int steps, double until) {
    build_lift(g);
    long f = orbit_bad(g) + 1000L * dup_count();
    for (int s = 0; s < steps && f > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd_);
        int old = dG[t];
        int nv = rndint(NN_);
        if (nv == old) continue;
        dG[t] = nv;
        build_lift(g);
        long nf = orbit_bad(g) + 1000L * dup_count();
        if (nf <= f || rnd01() < 0.01) f = nf;
        else dG[t] = old;
    }
    build_lift(g);
    return f;
}

static int lift_trial(Graph *out, int steps, double until) {
    static Graph cur;
    long f = climb(&cur, steps, until);
    if (f == 0 && is_valid(&cur)) {
        copy_graph(out, &cur);
        return 1;
    }
    return 0;
}

/* ------------------------------------------- phase 1: exhaustive bi-Cayley (d = 3) */

static int dist_a[MAXN], qu_a[MAXN];

/* Single-vertex-per-side bi-Cayley check: BFS from a_e and b_e. */
static int bc_ok(int N, const int *gs, const int *gi, int nd) {
    int nv = 2 * N;
    for (int s = 0; s < 2; s++) {
        int src = s ? N : 0;
        for (int v = 0; v < nv; v++) dist_a[v] = -1;
        int head = 0, tail = 0;
        dist_a[src] = 0;
        qu_a[tail++] = src;
        while (head < tail) {
            int v = qu_a[head++];
            if (dist_a[v] >= D) continue;
            for (int t = 0; t < nd; t++) {
                int u;
                if (v < N) u = N + MT[((unsigned)v << 9) | (unsigned)gs[t]];
                else u = MT[((unsigned)(v - N) << 9) | (unsigned)gi[t]];
                if (dist_a[u] < 0) {
                    dist_a[u] = dist_a[v] + 1;
                    qu_a[tail++] = u;
                }
            }
        }
        if (tail < nv) return 0;
    }
    return 1;
}

static void exhaustive_p1(Graph *best, double until) {
    static Graph cand;
    long lim = moore_bound();
    if (lim > MAXN) lim = MAXN;
    int N = best->n / 2 + 1;
    if (N < d + 1) N = d + 1;
    for (; now() < until && 2L * N <= lim && N < MAXG; N++) {
        list_groups(N);
        int found = 0, timeup = 0;
        for (int gg = 0; gg < ntri && !found && !timeup; gg++) {
            build_group(tris[gg].m, tris[gg].k, tris[gg].r);
            NN_ = N;
            P_ = 1;
            nd_ = 3;
            long cnt = 0;
            for (int a = 1; a < N && !found && !timeup; a++) {
                for (int b = a + 1; b < N; b++) {
                    if ((++cnt & 1023) == 0 && now() > until) { timeup = 1; break; }
                    int gs[3] = {0, a, b};
                    int gi[3] = {0, IV[a], IV[b]};
                    if (!bc_ok(N, gs, gi, 3)) continue;
                    for (int t = 0; t < 3; t++) {
                        dI[t] = 0;
                        dJ[t] = 0;
                        dG[t] = gs[t];
                    }
                    build_lift(&cand);
                    if (is_valid(&cand)) { found = 1; break; }
                }
            }
        }
        if (found && cand.n > best->n) copy_graph(best, &cand);
    }
}

/* -------------------------------------------- phase 2: random lifts, p = 1..3 */

static void random_phase(Graph *best, double until) {
    static Graph cand;
    long lim = moore_bound();
    if (lim > MAXN) lim = MAXN;
    while (now() < until) {
        long Nmin1 = best->n / 2 + 1;
        if (Nmin1 < d + 1) Nmin1 = d + 1;
        if (2 * Nmin1 > lim || Nmin1 >= MAXG) break;
        int r = rndint(8);
        int p = r < 2 ? 1 : (r < 6 ? 2 : 3);
        long Nmin = best->n / (2L * p) + 1;
        if (Nmin < d + 1) Nmin = d + 1;
        long N = Nmin + rndint(10);
        if (2L * p * N > lim || N >= MAXG) continue;
        list_groups((int)N);
        if (ntri == 0) continue;
        Tri t = tris[rndint(ntri)];
        build_group(t.m, t.k, t.r);
        P_ = p;
        NN_ = (int)N;
        for (int a = 0; a < 4 && now() < until; a++) {
            random_base();
            if (lift_trial(&cand, 4000, until) && cand.n > best->n)
                copy_graph(best, &cand);
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.90;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound() && best.n < MAXN) {
        double span = t_end - t0;
        if (d == 3) exhaustive_p1(&best, t0 + span * 0.35);
        random_phase(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
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

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.90 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
