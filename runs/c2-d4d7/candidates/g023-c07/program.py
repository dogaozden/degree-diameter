"""Bold variant for the weakest target (d=4, D=7): regular lifts over a different group mix.

Change from the parent: the C engine is rewritten around one search loop. Each attempt picks a
group order N just above the current best vertex count, then picks a group family (dihedral
D_N/2, semidirect Z_m x| Z_k, or abelian Z_m x Z_k), then anneals voltages of a random d-regular
base multigraph on p+p fibres (p = 1 or 2). The dihedral family is new: it gives non-metacyclic
bi-Cayley graphs that the parent never tried. The objective is the orbit-reduced excess distance,
computed by BFS from the 2p fibre identities only. Every accepted lift is re-checked with the full
all-pairs bitset test. The Python side keeps the best valid start (K_{d,d} or an algebraic graph)
and returns it whenever the engine fails, times out, or produces anything invalid.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Regular-lift degree-diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0".
 * stdout:  "n m" then m lines "u v": the largest valid graph found (or "0 0").
 *
 * Families of groups (order N, identity = element 0):
 *   kind 0: Z_m x Z_k          element a*k+b
 *   kind 1: dihedral of order 2m  element a*2+f  (a in Z_m, f in {0,1})
 *   kind 2: Z_m x|_r Z_k       element a*k+b, (a,b)(c,e) = (a + r^b c, b+e)
 * Lift: fibres A_i, B_j (i,j < p), vertex (fibre, x). Dart (i,j,g) joins A_i x to B_j (x*g).
 * Left multiplication is an automorphism, so BFS from the 2p fibre identities suffices.
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
#define MAXG 1100
#define MAXP 2
#define MAXDART (MAXD * MAXP)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;

typedef struct {
    int kind;
    int m, k, r;
    int rp[MAXG];
} Grp;

static int d, D;
static double t_end;
static int GN;
static int MT[MAXG * MAXG];
static Graph work, cand, best;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];
static int dist_[MAXN], qu_[MAXN];

static uint64_t rng_state = 88172645463325252ULL;
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
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

/* Number of unordered pairs at distance > D (bitset BFS). Fills badv. */
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
        badv[v] = n - c;
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
static int gmul(const Grp *G, int x, int y) {
    int m = G->m, k = G->k;
    if (G->kind == 0) {
        int a = x / k, b = x % k, c = y / k, e = y % k;
        return ((a + c) % m) * k + (b + e) % k;
    }
    if (G->kind == 1) {
        int a = x / 2, f = x % 2, b = y / 2, g = y % 2;
        int bb = f ? (m - b) % m : b;
        return ((a + bb) % m) * 2 + (f + g) % 2;
    }
    {
        int a = x / k, b = x % k, c = y / k, e = y % k;
        return (int)(((long)a + (long)G->rp[b] * c) % m) * k + (b + e) % k;
    }
}

static void set_group(const Grp *G, int N) {
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul(G, x, y);
}

/* fam 0: dihedral of order N; fam 1: abelian Z_m x Z_k; fam 2: semidirect product. */
static int make_group(Grp *G, int N, int fam) {
    if (fam == 0) {
        if (N % 2 || N < 4) return 0;
        G->kind = 1; G->m = N / 2; G->k = 2; G->r = 1;
        return 1;
    }
    static int divs[MAXG];
    int nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) divs[nd++] = m;
    if (fam == 1) {
        int m = divs[rndint(nd)];
        G->kind = 0; G->m = m; G->k = N / m; G->r = 1;
        return 1;
    }
    long count = 0;
    int bm = 0, br = 0, bk = 0;
    for (int t = 0; t < nd; t++) {
        int m = divs[t];
        if (m < 2) continue;
        int k = N / m;
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; br = r; bk = k; }
        }
    }
    if (!count) return 0;
    G->kind = 2; G->m = bm; G->k = bk; G->r = br;
    G->rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G->rp[b] = (int)((long)G->rp[b - 1] * br % bm);
    return 1;
}

/* ---------------------------------------------------------------- lifts */
/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
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
        if (nseen == 2 * p) return;
    }
}

static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, (p + dt[t].j) * N + MT[x * N + dt[t].g]);
}

/* Voltage for a new dart on (i,j) that differs from the other darts on the same pair. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced excess distance: BFS from each of the 2p fibre identities. Each vertex at
 * distance > D costs dist - D; an unreached vertex costs 2. Zero iff the lift has diameter <= D. */
static long excess(const Graph *g, int p) {
    int N = GN, nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[src] = 0;
        qu_[tail++] = src;
        while (head < tail) {
            int v = qu_[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_[u] < 0) {
                    dist_[u] = dist_[v] + 1;
                    qu_[tail++] = u;
                }
            }
        }
        for (int v = 0; v < nv; v++) {
            if (dist_[v] < 0) total += 2;
            else if (dist_[v] > D) total += dist_[v] - D;
        }
    }
    return total;
}

/* Simulated annealing over the voltages of one random base over the current group. Returns 1 and
 * writes a verified graph to out if a valid lift is found. */
static int try_lift(Graph *out, int p, int steps, double until) {
    static Dart dt[MAXDART], bestdt[MAXDART];
    int M[MAXP][MAXP], N = GN, nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(&work, p, dt, nd);
    long cur = excess(&work, p), best_e = cur;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    double T0 = 1.0 + 0.05 * (double)cur, T = T0;
    int stall = 0;
    for (int s = 0; s < steps && best_e > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        int t = rndint(nd), old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(&work, p, dt, nd);
        long nv = excess(&work, p);
        long delta = nv - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nv;
        else dt[t].g = old;
        if (cur < best_e) {
            best_e = cur;
            memcpy(bestdt, dt, sizeof(Dart) * nd);
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.9993;
        if (T < 0.3) T = 0.3;
        if (stall > 1500 && best_e > 0) {
            memcpy(dt, bestdt, sizeof(Dart) * nd);
            for (int k = 0; k < 2; k++) {
                int u = rndint(nd);
                dt[u].g = fresh_voltage(dt, nd, u, dt[u].i, dt[u].j, N);
            }
            build_lift(&work, p, dt, nd);
            cur = excess(&work, p);
            T = T0;
            stall = 0;
        }
    }
    if (best_e != 0) return 0;
    build_lift(&work, p, bestdt, nd);
    if (!is_valid(&work)) return 0;
    copy_graph(out, &work);
    return 1;
}

/* Repeatedly try lifts of order 2pN just above the current best, across group families. */
static void search(Graph *bst, double until) {
    static Grp G;
    long moore = moore_bound();
    long vmax = moore < MAXN ? moore : MAXN;
    while (now() < until) {
        if ((long)bst->n >= vmax) return;
        int p = rndint(10) < 7 ? 1 : 2;
        long nlo = bst->n / (2 * p) + 1;
        long nhi = vmax / (2 * p);
        if (nhi > MAXG) nhi = MAXG;
        if (nlo > nhi) continue;
        long slack = 3 + nlo / 12;
        long span = nhi - nlo + 1;
        if (span > slack) span = slack;
        long N = nlo + rndint((int)span);
        if (N < d) N = d;
        if (N > nhi) continue;
        int fam = rndint(10);
        int fk = fam < 4 ? 0 : (fam < 7 ? 2 : 1);
        if (fk == 0 && (N % 2) && N + 1 <= nhi) N++;
        if (!make_group(&G, (int)N, fk)) continue;
        set_group(&G, (int)N);
        if (try_lift(&cand, p, 10000, until) && cand.n > bst->n) copy_graph(bst, &cand);
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

    if (d < 1 || D < 2 || d > MAXD - 1) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    search(&best, t_end);
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

    A candidate is kept only if it passes lib.is_valid with diameter 6. Returns None if nothing
    verifies.
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
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
