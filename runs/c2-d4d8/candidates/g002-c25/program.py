"""Group-lift search for the weakest case (d=4, D=8 and similar).

New in this version: the C engine lifts base multigraphs (1-3 vertices per side) over
finite groups given by multiplication tables. Groups are the matrix groups SL(2,p),
PSL(2,p) and PGL(2,p) for small primes p, plus the semidirect products Z_m x| Z_k used
before. Matrix groups are built from 2x2 matrices, so orders such as 1092 (PSL(2,13),
record 2184 = 2 * 1092) and 2448 (PSL(2,17)) are available. Left multiplication acts
regularly on every fibre, so the diameter check needs BFS only from one representative
per fibre. Python builds the algebraic starts, validates them, and falls back to the best
valid graph so every case returns a valid output.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Group-lift degree-diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Base multigraph on p + p fibres (p <= 3), d-regular. Each fibre is a copy of a finite group G
 * (order N). Dart (i, j, g) joins A(i,x) to B(j, x*g). Groups: SL(2,q), PSL(2,q), PGL(2,q) for
 * small primes q (multiplication table built from matrices), and semidirect products
 * Z_m x|_r Z_k. Orbit-reduced diameter test: BFS from one representative per fibre.
 */
#define _POSIX_C_SOURCE 200809L
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXG 2500
#define MAXP 3

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

static void del_half(Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) {
            g->adj[u][i] = g->adj[u][--g->deg[u]];
            return;
        }
}

static void del_edge(Graph *g, int u, int v) {
    del_half(g, u, v);
    del_half(g, v, u);
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
static int badv[MAXN];

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

/* ------------------------------------------------------------ group tables */

/* MT[x*N + y] = index of x*y. Element 0 is the identity. */
static uint16_t MT[MAXG * MAXG];
static int GN = 0;

static int mcode(int a, int b, int c, int e, int q) {
    return ((a * q + b) * q + c) * q + e;
}

static int invmod(int x, int q) {
    long r = 1, b = ((x % q) + q) % q, ex = q - 2;
    while (ex > 0) {
        if (ex & 1) r = r * b % q;
        b = b * b % q;
        ex >>= 1;
    }
    return (int)r;
}

/* Canonical code of a matrix class. kind 1 = SL(2,q), 2 = PSL(2,q) = SL/{+-1},
 * 3 = PGL(2,q) = GL/scalars (first nonzero entry scaled to 1). */
static int canon(int kind, int q, int a, int b, int c, int e) {
    if (kind == 1) return mcode(a, b, c, e, q);
    if (kind == 2) {
        int c1 = mcode(a, b, c, e, q);
        int c2 = mcode((q - a) % q, (q - b) % q, (q - c) % q, (q - e) % q, q);
        return c1 < c2 ? c1 : c2;
    }
    int f = a ? a : (b ? b : (c ? c : e));
    int iv = invmod(f, q);
    return mcode(a * iv % q, b * iv % q, c * iv % q, e * iv % q, q);
}

static int idxmap[83521];
static int el[MAXG][4];

static int matrix_group(int kind, int q) {
    int tot = q * q * q * q;
    if (tot > 83521) return 0;
    for (int i = 0; i < tot; i++) idxmap[i] = -1;
    int N = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    int det = ((a * e - b * c) % q + q) % q;
                    if (kind == 3 ? det == 0 : det != 1) continue;
                    if (canon(kind, q, a, b, c, e) != mcode(a, b, c, e, q)) continue;
                    if (N >= MAXG) return 0;
                    el[N][0] = a; el[N][1] = b; el[N][2] = c; el[N][3] = e;
                    N++;
                }
    int idc = canon(kind, q, 1, 0, 0, 1);
    int pos = -1;
    for (int i = 0; i < N; i++)
        if (mcode(el[i][0], el[i][1], el[i][2], el[i][3], q) == idc) { pos = i; break; }
    if (pos < 0) return 0;
    if (pos != 0)
        for (int t = 0; t < 4; t++) {
            int s = el[0][t];
            el[0][t] = el[pos][t];
            el[pos][t] = s;
        }
    for (int i = 0; i < N; i++)
        idxmap[mcode(el[i][0], el[i][1], el[i][2], el[i][3], q)] = i;
    for (int x = 0; x < N; x++) {
        int a = el[x][0], b = el[x][1], c = el[x][2], e = el[x][3];
        for (int y = 0; y < N; y++) {
            int A = el[y][0], B = el[y][1], C = el[y][2], E = el[y][3];
            int p00 = (a * A + b * C) % q, p01 = (a * B + b * E) % q;
            int p10 = (c * A + e * C) % q, p11 = (c * B + e * E) % q;
            int id = idxmap[canon(kind, q, p00, p01, p10, p11)];
            if (id < 0) return 0;
            MT[x * N + y] = (uint16_t)id;
        }
    }
    GN = N;
    return N;
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static int semidirect_group(int m, int k, int r) {
    int N = m * k;
    if (N < 1 || N > MAXG) return 0;
    static int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long z = ((a + (long)rp[b] * c) % m) * k + (b + e) % k;
            MT[x * N + y] = (uint16_t)z;
        }
    }
    GN = N;
    return N;
}

static int random_semidirect(int N, int *Mo, int *Ko, int *Ro) {
    long count = 0;
    int bm = -1, bk = -1, br = -1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (bm < 0) return 0;
    *Mo = bm; *Ko = bk; *Ro = br;
    return 1;
}

typedef struct { int kind, q, N; } MPool;
static MPool pool[16];
static int npool = 0;

static void init_pool(void) {
    int qs[5] = {5, 7, 11, 13, 17};
    for (int kind = 1; kind <= 3; kind++)
        for (int t = 0; t < 5; t++) {
            int q = qs[t];
            int N = (kind == 2) ? q * (q * q - 1) / 2 : q * (q * q - 1);
            if (N <= MAXG && npool < 16) {
                pool[npool].kind = kind;
                pool[npool].q = q;
                pool[npool].N = N;
                npool++;
            }
        }
}

/* ------------------------------------------------------------- lifts */

typedef struct { int i, j, g; } Dart;

static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++) {
            int a = dt[t].i * N + x;
            int b = p * N + dt[t].j * N + (int)MT[x * N + dt[t].g];
            add_edge(g, a, b);
        }
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced objective: BFS from one element-0 representative per fibre. Returns the number
 * of (representative, vertex) pairs at distance > D. Zero iff the lift has diameter <= D. */
static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
    long total = 0;
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

/* Hill-climb the voltages of one random base multigraph over the current group table. */
static int lift_try(Graph *g, int p, int N, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, dt, nd);
    return bad == 0;
}

/* Ladder search over lifts strictly larger than the current best. Each attempt picks a group
 * (a matrix group from the pool, or a random semidirect product) near the frontier. The
 * step adapts: success doubles it, failure halves it. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    if (moore > MAXN) moore = MAXN;
    long step = 4;
    while (now() < until) {
        if (best->n + 2 > moore) break;
        int r = rndint(10);
        int p = r < 6 ? 1 : (r < 9 ? 2 : 3);
        long maxN = moore / (2 * p);
        if (maxN > MAXG) maxN = MAXG;
        long minN = best->n / (2 * p) + 1;
        if (minN > maxN || maxN < 2 * d) continue;

        int N = 0;
        if (rnd01() < 0.35) {
            int cnt = 0, pick = -1;
            for (int k = 0; k < npool; k++)
                if (pool[k].N >= minN && pool[k].N <= maxN && rndint(++cnt) == 0) pick = k;
            if (pick >= 0) N = matrix_group(pool[pick].kind, pool[pick].q);
        }
        if (N == 0) {
            long span = maxN - minN;
            long lim = step < span ? step : span;
            long want = minN + (long)rndint((int)lim + 1);
            if (want < 2 * d) want = 2 * d;
            if (want > maxN) want = maxN;
            int m, k, rr;
            if (!random_semidirect((int)want, &m, &k, &rr)) continue;
            N = semidirect_group(m, k, rr);
            if (N == 0) continue;
        }
        int ok = 0;
        if (lift_try(&cand, p, N, 2500, until) && is_valid(&cand) && cand.n > best->n) {
            copy_graph(best, &cand);
            ok = 1;
        }
        if (ok) {
            if (step < 2048) step *= 2;
        } else if (step > 1) {
            step /= 2;
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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    init_pool();
    if (D >= 2 && d >= 3 && best.n < moore_bound())
        lift_search(&best, t_end);
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

    budget = 0.8 * time_limit - 2.0 - (time.monotonic() - t0)
    if budget < 2.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10.0)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
