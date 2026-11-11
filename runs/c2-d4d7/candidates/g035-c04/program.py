"""Bi-Cayley voltage lifts over cyclic, abelian and semidirect groups, found by annealing.

Change from the parent: the C engine no longer climbs with a fixed Z_m x| Z_k hill-climb or
grow-by-two annealing. It builds each lift over a freshly drawn group of order N, with
N chosen so the lifted order 2pN sits just above the current best. Voltages on a random
d-regular base multigraph with p <= 4 vertices per side are annealed (Metropolis on the
orbit-reduced count of bad pairs), with restarts from the elite. Accepted graphs are re-checked
with a full all-pairs bitset test. Start graphs come from the Python side (projective plane,
W(q), and the split Cayley hexagon H(3) with 728 vertices for d=4, D>=6). If the C engine fails,
the Python fallback is returned. Untested in this form: the search may not reach the parent's
840 for d=4, D=7, so validate before relying on it.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley / voltage-lift search by simulated annealing over group voltages.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A lift has 2pN vertices: A-fibres i in [0,p), B-fibres j in [0,p), group elements x in Z_N-like G.
 * Edge (A_i,x) -- (B_j, x*g) for each dart (i,j,g) of a random d-regular base multigraph.
 * The group acts regularly by left multiplication, so the diameter test needs only BFS from the
 * 2p fibre identities.
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
#define MAXG 2048
#define MAXP 4
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

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
    if (b < 0) b += m;
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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
static long bad_pairs(const Graph *g) {
    int n = g->n, W = (n + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * W);
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
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
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
                if (g->side[u] == 255) { g->side[u] = (unsigned char)(1 - g->side[v]); queue[tail++] = u; }
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
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= d); }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ---------------------------------------------------------------- groups
 * Group of order GN as a full multiplication table GT[x*GN+y], identity 0. */
static int GN;
static int GT[MAXG * MAXG];
static int rp[MAXG];

static void set_cyclic(int N) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            GT[x * N + y] = (x + y) % N;
}

/* Z_m x Z_k, element a*k+b. */
static void set_abelian(int m, int k) {
    int N = m * k;
    GN = N;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = ((a + c) % m) * k + (b + e) % k;
        }
    }
}

/* Z_m x|_r Z_k: (a,b)(c,e) = (a + r^b c, b + e), needs r^k = 1 mod m. */
static void set_semidirect(int m, int k, int r) {
    int N = m * k;
    GN = N;
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
}

static void apply_group(int type, int m, int k, int r, int N) {
    if (type == 0) set_cyclic(N);
    else if (type == 1) set_abelian(m, k);
    else set_semidirect(m, k, r);
}

/* Draw a random group of order N: cyclic, abelian with a random factorisation, or semidirect. */
static void random_group(int N, int *type, int *m, int *k, int *r) {
    int divs[64], nd = 0;
    for (int x = 1; x <= N && nd < 64; x++)
        if (N % x == 0) divs[nd++] = x;
    int t = rndint(3);
    int mm = divs[rndint(nd)];
    if (t == 0) { *type = 0; *m = N; *k = 1; *r = 0; return; }
    *type = 1;
    *m = mm;
    *k = N / mm;
    *r = 0;
    if (t == 2 && mm > 1) {
        for (int tries = 0; tries < 200; tries++) {
            int rr = rndint(mm);
            if (gcd(rr, mm) != 1) continue;
            if (powmod(rr, *k, mm) != 1 % mm) continue;
            *type = 2;
            *r = rr;
            break;
        }
    }
}

/* ---------------------------------------------------------------- voltage lifts */

/* Random d-regular bipartite multigraph on p + p vertices, connected. */
static int make_base(int p, int M[MAXP][MAXP]) {
    for (int attempt = 0; attempt < 2000; attempt++) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP];
        memset(seen, 0, sizeof seen);
        int stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p]) : (u < p && M[u][v - p]);
                if (linked) { seen[u] = 1; nseen++; stack[top++] = u; }
            }
        }
        if (nseen == 2 * p) return 1;
    }
    return 0;
}

/* A fresh voltage for dart slot `skip` on pair (i,j) that does not duplicate another dart. */
static int fresh_g(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (int tries = 0; tries < 100000; tries++) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return -1;
}

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced objective: BFS from the 2p fibre identities; returns the number of
 * (representative, vertex) pairs at distance > D. Zero iff the lift has diameter <= D. */
static long orbit_bad(const Graph *g, int p, int N) {
    long total = 0;
    int nv = g->n;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            if (dist_buf[v] >= D) continue;
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        total += nv - tail;
    }
    return total;
}

static Graph cand;
static Graph outg;

/* Simulated annealing over the voltages of one random base multigraph over the current group.
 * Runs in rounds of R steps with a cooling temperature; each round restarts from the elite with
 * two perturbed darts. Returns 1 and fills `out` with a verified valid lift on success. */
static int anneal_lift(Graph *out, int p, int N, double until) {
    int M[MAXP][MAXP];
    static Dart dt[MAXDART], best_dt[MAXDART];
    if (!make_base(p, M)) return 0;
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_g(dt, nd, -1, i, j, N);
                if (dt[nd].g < 0) return 0;
                nd++;
            }
    Graph *g = &cand;
    build_lift(g, p, N, dt, nd);
    long bad = orbit_bad(g, p, N);
    long bestbad = bad;
    memcpy(best_dt, dt, sizeof(Dart) * nd);
    const int R = 6000;
    while (bestbad > 0 && now() < until) {
        for (int it = 0; it < R && bestbad > 0; it++) {
            if ((it & 63) == 0 && now() > until) break;
            double T = 1.5 * pow(0.02, (double)it / R) + 0.02;
            int t = rndint(nd);
            int old = dt[t].g;
            int ng = fresh_g(dt, nd, t, dt[t].i, dt[t].j, N);
            if (ng < 0) continue;
            dt[t].g = ng;
            build_lift(g, p, N, dt, nd);
            long nb = orbit_bad(g, p, N);
            if (nb <= bad || rnd01() < exp(-(double)(nb - bad) / T)) {
                bad = nb;
                if (bad < bestbad) {
                    bestbad = bad;
                    memcpy(best_dt, dt, sizeof(Dart) * nd);
                }
            } else {
                dt[t].g = old;
            }
        }
        /* restart from the elite with two perturbed darts */
        memcpy(dt, best_dt, sizeof(Dart) * nd);
        for (int k = 0; k < 2; k++) {
            int u = rndint(nd);
            int ng = fresh_g(dt, nd, u, dt[u].i, dt[u].j, N);
            if (ng >= 0) dt[u].g = ng;
        }
        build_lift(g, p, N, dt, nd);
        bad = orbit_bad(g, p, N);
    }
    if (bestbad == 0) {
        memcpy(dt, best_dt, sizeof(Dart) * nd);
        build_lift(g, p, N, dt, nd);
        if (is_valid(g)) {
            copy_graph(out, g);
            return 1;
        }
    }
    return 0;
}

/* Climb: each attempt targets lifts of order just above the current best. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && fails < 500) {
        long cur = best->n;
        if (cur + 2 > moore) break;
        int p = 1 + rndint(MAXP);
        long Nlo = cur / (2L * p) + 1;
        if (Nlo < d + 1) Nlo = d + 1;
        long win = Nlo / 12 + 3;
        long N = Nlo + rndint((int)win);
        if (2L * p * N > moore || 2L * p * N > MAXN || N > MAXG) { fails++; continue; }
        int type, m, k, r;
        random_group((int)N, &type, &m, &k, &r);
        apply_group(type, m, k, r, (int)N);
        double left = until - now();
        double slice = left / 4.0;
        if (slice > 6.0) slice = 6.0;
        if (slice < 0.5) slice = 0.5;
        double lim = now() + slice;
        if (lim > until) lim = until;
        if (anneal_lift(&outg, p, (int)N, lim) && outg.n > best->n) {
            copy_graph(best, &outg);
            fails = 0;
        } else {
            fails++;
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 2 || d > MAXD || D < 2) {
        if (d >= 1 && d <= MAXD) complete_bipartite(&best);
        else { best.n = 1; best.deg[0] = 0; best.side[0] = 0; }
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore_bound()) lift_search(&best, t_end);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


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
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand_graph in known_starts(d, D):
        n, e = cand_graph
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
