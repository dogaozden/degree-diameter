"""Bi-Cayley voltage search over explicit groups, with a best-known safe fallback.

This island's bold change: instead of semidirect-product lifts, the C engine searches
bi-Cayley-type lifts over several explicit groups: cyclic Z_N, semidirect Z_m x| Z_k,
affine groups AGL(1,q) for prime q, and SL(2,p) and PSL(2,p) for p in {3,5,7}.
The group is given by a multiplication table built in C.

Construction: KB base vertices per side (KB = 1, 2, 3). Layer 0 is fixed to the identity
(relabelling makes this WLOG), and layers 1..d-1 carry a permutation of the base vertices
plus a group voltage per base vertex. Left multiplication is an automorphism, so the
diameter is <= D iff a BFS of depth D from each of the 2*KB class representatives reaches
everything. Voltages and permutations are annealed on the number of unreached pairs.
Each success is re-checked by an explicit full-graph validity test in C, and Python checks
it again with lib.is_valid. Any failure falls back to the best known start (Moore graph,
Araujo-Pardo-Lopez, generalized quadrangle, or K_{d,d}).

Timing: C uses 96% of its own budget. Python passes 95% of time_limit minus a 1.5 s margin
for compilation and process startup. The subprocess timeout is budget + 2.5 s.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley / voltage-lift search over explicit groups.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXK 3
#define MAXG 400
#define MAXV (2 * MAXK * MAXG)
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

static int is_prime_i(int x) {
    if (x < 2) return 0;
    for (int k = 2; k * k <= x; k++)
        if (x % k == 0) return 0;
    return 1;
}

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ graph basics */

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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Explicit validity test: degree, bipartite, simple, diameter <= D. */
static int fvis[MAXN], fq[MAXN], fst = 0;
static int full_valid(const Graph *g) {
    int n = g->n;
    if (n <= 0 || n > MAXN) return 0;
    for (int v = 0; v < n; v++) {
        if (g->deg[v] > d) return 0;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (u < 0 || u >= n || u == v || g->side[u] == g->side[v]) return 0;
            for (int j = 0; j < i; j++)
                if (g->adj[v][j] == u) return 0;
        }
    }
    for (int s = 0; s < n; s++) {
        fst++;
        int head = 0, tail = 0;
        fq[tail++] = s;
        fvis[s] = fst;
        for (int dep = 0; dep < D && head < tail; dep++) {
            int end = tail;
            while (head < end) {
                int u = fq[head++];
                for (int i = 0; i < g->deg[u]; i++) {
                    int v = g->adj[u][i];
                    if (fvis[v] != fst) { fvis[v] = fst; fq[tail++] = v; }
                }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
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
    if (!full_valid(g)) g->n = 0;
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

/* ------------------------------------------------------------ groups */

static int NG, GID;
static int GMUL[MAXG][MAXG];
static int GINV[MAXG];

/* Find the identity and inverses. Returns 0 if the table is not a group-like table. */
static int finish_group(void) {
    GID = -1;
    for (int x = 0; x < NG && GID < 0; x++) {
        int ok = 1;
        for (int y = 0; y < NG && ok; y++)
            if (GMUL[x][y] != y) ok = 0;
        if (ok) GID = x;
    }
    if (GID < 0) return 0;
    for (int x = 0; x < NG; x++) {
        GINV[x] = -1;
        for (int y = 0; y < NG; y++)
            if (GMUL[x][y] == GID) { GINV[x] = y; break; }
        if (GINV[x] < 0) return 0;
    }
    return 1;
}

static int set_cyclic(int N) {
    NG = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            GMUL[x][y] = (x + y) % N;
    return finish_group();
}

/* Z_m x|_r Z_k: element a*k+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k). */
static int set_semidirect(int m, int k, int r) {
    NG = m * k;
    int RP[MAXG];
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < NG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < NG; y++) {
            int c = y / k, e = y % k;
            int aa = (int)(((long)a + (long)RP[b] * c) % m);
            int bb = (b + e) % k;
            GMUL[x][y] = aa * k + bb;
        }
    }
    return finish_group();
}

/* AGL(1,q), q prime: maps x -> a x + b; element (a,b) coded as (a-1)*q + b. */
static int set_agl(int q) {
    NG = q * (q - 1);
    for (int x = 0; x < NG; x++) {
        int ax = x / q + 1, bx = x % q;
        for (int y = 0; y < NG; y++) {
            int ay = y / q + 1, by = y % q;
            int a = ax * ay % q;
            int b = (ax * by + bx) % q;
            GMUL[x][y] = (a - 1) * q + b;
        }
    }
    return finish_group();
}

/* SL(2,p) or PSL(2,p) = SL(2,p)/{+-I}, p prime <= 7. */
static int SREP[MAXG][4];
static int KIDX[2401], LOOK[2401];

static int sl_code(int a, int b, int c, int e, int p) {
    return ((a * p + b) * p + c) * p + e;
}

static int sl_key(int a, int b, int c, int e, int p, int psl) {
    int code = sl_code(a, b, c, e, p);
    if (!psl) return code;
    int ncode = sl_code((p - a) % p, (p - b) % p, (p - c) % p, (p - e) % p, p);
    return code < ncode ? code : ncode;
}

static int set_sl2(int p, int psl) {
    int P4 = p * p * p * p;
    for (int i = 0; i < P4; i++) { KIDX[i] = -1; LOOK[i] = -1; }
    int n = 0;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    if ((((a * e - b * c) % p) + p) % p != 1) continue;
                    int key = sl_key(a, b, c, e, p, psl);
                    if (KIDX[key] < 0) {
                        if (n >= MAXG) return 0;
                        KIDX[key] = n;
                        SREP[n][0] = a; SREP[n][1] = b; SREP[n][2] = c; SREP[n][3] = e;
                        n++;
                    }
                }
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    if ((((a * e - b * c) % p) + p) % p != 1) continue;
                    LOOK[sl_code(a, b, c, e, p)] = KIDX[sl_key(a, b, c, e, p, psl)];
                }
    NG = n;
    for (int x = 0; x < NG; x++) {
        int m00 = SREP[x][0], m01 = SREP[x][1], m10 = SREP[x][2], m11 = SREP[x][3];
        for (int y = 0; y < NG; y++) {
            int n00 = SREP[y][0], n01 = SREP[y][1], n10 = SREP[y][2], n11 = SREP[y][3];
            int P0 = (m00 * n00 + m01 * n10) % p;
            int P1 = (m00 * n01 + m01 * n11) % p;
            int P2 = (m10 * n00 + m11 * n10) % p;
            int P3 = (m10 * n01 + m11 * n11) % p;
            GMUL[x][y] = LOOK[sl_code(P0, P1, P2, P3, p)];
        }
    }
    return finish_group();
}

/* Choose a random group of order N among the families available for N. */
static int pick_group(int N) {
    if (N < 3) return 0;
    int opt[5], no = 0;
    opt[no++] = 0;
    int sm = 0, sk = 0, sr = 0;
    for (int t = 0; t < 60; t++) {
        int m = 3 + rndint(N - 2);
        if (N % m) continue;
        int k = N / m;
        if (k < 2) continue;
        int r = 2 + rndint(m - 2);
        if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
        sm = m; sk = k; sr = r;
        break;
    }
    if (sm) opt[no++] = 1;
    int qa = 0;
    for (int q = 2; q * (q - 1) <= N; q++)
        if (q * (q - 1) == N && is_prime_i(q)) qa = q;
    if (qa) opt[no++] = 2;
    int sp = 0, spsl = 0;
    for (int p = 3; p <= 7; p += 2) {
        if (!is_prime_i(p)) continue;
        if (N == p * (p * p - 1)) sp = p;
        if (2 * N == p * (p * p - 1)) spsl = p;
    }
    if (sp) opt[no++] = 3;
    if (spsl) opt[no++] = 4;
    int c = opt[rndint(no)];
    switch (c) {
        case 0: return set_cyclic(N);
        case 1: return set_semidirect(sm, sk, sr);
        case 2: return set_agl(qa);
        case 3: return set_sl2(sp, 0);
        default: return set_sl2(spsl, 1);
    }
}

/* ------------------------------------------------------------ voltage lifts */

/* Vertices: A(i,g) = i*NG+g, B(j,x) = (KB+j)*NG+x.
 * Layer l, base vertex i: A(i,g) ~ B(DJ[l][i], g * DS[l][i]).
 * Layer 0 is fixed to DJ=i, DS=identity (WLOG by relabelling). */
static int KB;
static int DJ[MAXD][MAXK], DS[MAXD][MAXK], DSI[MAXD][MAXK], DIDX[MAXD][MAXK];
static int visst[MAXV], vst = 0, QQ[MAXV];

static void refresh_layer(int l) {
    for (int i = 0; i < KB; i++) {
        DSI[l][i] = GINV[DS[l][i]];
        DIDX[l][DJ[l][i]] = i;
    }
}

static void init_layers(void) {
    for (int i = 0; i < KB; i++) { DJ[0][i] = i; DS[0][i] = GID; }
    refresh_layer(0);
    for (int l = 1; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < KB; i++) p[i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = p[i]; p[i] = p[j]; p[j] = s;
        }
        for (int i = 0; i < KB; i++) {
            DJ[l][i] = p[i];
            DS[l][i] = rndint(NG);
        }
        refresh_layer(l);
    }
}

/* Two darts from the same base vertex with the same target and voltage give a multi-edge. */
static int dup_bad(void) {
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (DJ[l1][i] == DJ[l2][i] && DS[l1][i] == DS[l2][i]) return 1;
    return 0;
}

/* Unreached vertices in a BFS of depth D from src. */
static int bfs_unreached(int src) {
    int NV = 2 * KB * NG;
    int KN = KB * NG;
    vst++;
    int head = 0, tail = 0;
    QQ[tail++] = src;
    visst[src] = vst;
    for (int dep = 0; dep < D && head < tail; dep++) {
        int end = tail;
        while (head < end) {
            int u = QQ[head++];
            if (u < KN) {
                int i = u / NG, g = u - i * NG;
                for (int l = 0; l < d; l++) {
                    int v = KN + DJ[l][i] * NG + GMUL[g][DS[l][i]];
                    if (visst[v] != vst) { visst[v] = vst; QQ[tail++] = v; }
                }
            } else {
                int w = u - KN;
                int j = w / NG, x = w - j * NG;
                for (int l = 0; l < d; l++) {
                    int i = DIDX[l][j];
                    int v = i * NG + GMUL[x][DSI[l][i]];
                    if (visst[v] != vst) { visst[v] = vst; QQ[tail++] = v; }
                }
            }
        }
    }
    return NV - tail;
}

static long cost_now(void) {
    if (dup_bad()) return BIGCOST;
    long tot = 0;
    for (int i = 0; i < KB; i++) tot += bfs_unreached(i * NG + GID);
    for (int j = 0; j < KB; j++) tot += bfs_unreached((KB + j) * NG + GID);
    return tot;
}

/* Anneal layers on unreached-pair count. Returns the final cost (0 means success). */
static long climb(long steps) {
    init_layers();
    long cur = cost_now();
    if (d < 2) return cur;
    for (long s = 0; s < steps && cur > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) break;
        double T = 1.5 * (1.0 - (double)s / (double)steps) + 0.05;
        int l = 1 + rndint(d - 1);
        if (KB < 2 || rnd01() < 0.7) {
            int i = rndint(KB);
            int old = DS[l][i];
            int nv = rndint(NG);
            if (nv == old) continue;
            DS[l][i] = nv;
            refresh_layer(l);
            long c2 = cost_now();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else { DS[l][i] = old; refresh_layer(l); }
        } else {
            int i1 = rndint(KB), i2 = rndint(KB);
            if (i1 == i2) continue;
            int tmp = DJ[l][i1]; DJ[l][i1] = DJ[l][i2]; DJ[l][i2] = tmp;
            refresh_layer(l);
            long c2 = cost_now();
            if (c2 <= cur || rnd01() < exp(-(double)(c2 - cur) / T)) cur = c2;
            else {
                tmp = DJ[l][i1]; DJ[l][i1] = DJ[l][i2]; DJ[l][i2] = tmp;
                refresh_layer(l);
            }
        }
    }
    return cur;
}

static void build_full(Graph *g) {
    int KN = KB * NG;
    g->n = 2 * KN;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= KN; }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++)
            for (int x = 0; x < NG; x++)
                add_edge(g, i * NG + x, KN + DJ[l][i] * NG + GMUL[x][DS[l][i]]);
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.96;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, cand;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    long moore = moore_bound();
    int dead = 0;
    while (now() < t_end && best.n < moore) {
        int r = rndint(10);
        int kb = r < 5 ? 1 : (r < 8 ? 2 : 3);
        long hi = moore / (2L * kb);
        if (hi > MAXG - 1) hi = MAXG - 1;
        long lo = best.n / (2L * kb) + 1;
        if (lo > hi) {
            if (++dead > 200) break;
            continue;
        }
        long N;
        if (hi - lo > 40 && rndint(2) == 0) N = hi - rndint(40);
        else N = lo + rndint((int)(hi - lo + 1));
        if (!pick_group((int)N)) continue;
        KB = kb;
        int ok = 0;
        for (int rep = 0; rep < 6 && !ok && now() < t_end; rep++) {
            if (climb(6000) == 0) {
                build_full(&cand);
                if (cand.n > best.n && full_valid(&cand)) {
                    copy_graph(&best, &cand);
                    ok = 1;
                }
            }
        }
    }
    if (!full_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.95 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
