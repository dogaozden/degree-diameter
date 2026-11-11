"""Bi-Cayley search for the weakest target (d=4, D=7).

Change from the parent: the parent searched voltage lifts over a 2-vertex or p-vertex base and
evaluated whole lifted graphs. This version searches bi-Cayley graphs instead. For a finite group G
of order N, the graph has parts A = G and B = G, with (A,x) adjacent to (B,y) iff x^-1 y lies in a
d-subset S of G. Left translation acts transitively on each part, so the diameter is at most D iff
the eccentricity of (A,e) and of (B,e) is at most D. Each evaluation is therefore two BFS passes over
2N vertices. Simulated annealing over S then runs far faster than the parent's full-graph checks.
Groups are metacyclic Z_m x| Z_k for all valid r, plus PSL(2,7) x Z_k and PGL(2,7) x Z_k, which are
non-metacyclic. Every returned graph is re-checked by the all-pairs bitset test. If nothing better is
found, the best valid start graph (or K_{d,d}) is returned.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley degree-diameter search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Vertices A_x = x and B_y = N + y for x, y in G. Edge (A_x, B_{x s}) for s in S, |S| = d.
 * Left translation is an automorphism, so only the eccentricities of A_e and B_e matter.
 * Objective: sum over those two sources of max(0, dist - D), with unreached vertices charged 2.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 2048
#define MAXD 16
#define MAXW (MAXN / 64)
#define MAXG 1100
#define MAXV (2 * MAXG)
#define MAXDESC 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int kind; /* 0 semidirect Z_m x| Z_k, 1 PSL(2,7) x Z_k, 2 PGL(2,7) x Z_k */
    int m, k, r;
} GDesc;

static int d, D;
static double t_stop;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= d);
    }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* Full all-pairs check: number of unordered pairs at distance > D (bitset BFS). */
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

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

static int bfs_queue[MAXN];

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) {
        g->deg[v] = 0;
        g->side[v] = 255;
    }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        bfs_queue[tail++] = s;
        while (head < tail) {
            int v = bfs_queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    bfs_queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

/* ---------------------------------------------------------------- group tables
 * GT[x*N+y] = x*y, identity is index 0, INV[x] = x^-1. */
static int N;
static int GT[MAXG * MAXG];
static int INV[MAXG];

static void finish_group(void) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (GT[x * N + y] == 0) INV[x] = y;
}

/* Z_m x| Z_k: (a,b)(c,e) = (a + r^b c mod m, b + e mod k), element a*k + b. */
static void set_semidirect(int m, int k, int r) {
    N = m * k;
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            GT[x * N + y] = (int)((((long)a + (long)rp[b] * c) % m) * k + (b + e) % k);
        }
    }
    finish_group();
}

/* Permutation groups PSL(2,7) (pgl = 0) and PGL(2,7) (pgl = 1) on P^1(F_7), point 7 = infinity.
 * The table is the closure of the generators, so it is a genuine finite group even if the order
 * differs from the textbook value. */
static int BTAB[2][336 * 336];
static int BORD[2];
static unsigned char EP[336][8];

static int build_perm_base(int pgl, int *tab) {
    unsigned char gens[3][8];
    int ng = 2;
    for (int x = 0; x < 8; x++) gens[0][x] = (unsigned char)(x == 7 ? 7 : (x + 1) % 7);
    for (int x = 0; x < 8; x++) {
        int v;
        if (x == 7) v = 0;
        else if (x == 0) v = 7;
        else v = (7 - (int)powmod(x, 5, 7)) % 7;
        gens[1][x] = (unsigned char)v;
    }
    if (pgl) {
        ng = 3;
        for (int x = 0; x < 8; x++) gens[2][x] = (unsigned char)(x == 7 ? 7 : (3 * x) % 7);
    }
    int cnt = 1;
    for (int x = 0; x < 8; x++) EP[0][x] = (unsigned char)x;
    for (int qi = 0; qi < cnt; qi++) {
        for (int g = 0; g < ng; g++) {
            unsigned char h[8];
            for (int x = 0; x < 8; x++) h[x] = EP[qi][gens[g][x]];
            int found = 0;
            for (int j = 0; j < cnt && !found; j++) found = (memcmp(EP[j], h, 8) == 0);
            if (!found) {
                if (cnt >= 336) return 0;
                memcpy(EP[cnt], h, 8);
                cnt++;
            }
        }
    }
    for (int i = 0; i < cnt; i++) {
        for (int j = 0; j < cnt; j++) {
            unsigned char h[8];
            for (int x = 0; x < 8; x++) h[x] = EP[i][EP[j][x]];
            int idx = -1;
            for (int t = 0; t < cnt && idx < 0; t++)
                if (memcmp(EP[t], h, 8) == 0) idx = t;
            tab[i * cnt + j] = idx < 0 ? 0 : idx;
        }
    }
    return cnt;
}

static void init_perm_bases(void) {
    BORD[0] = build_perm_base(0, BTAB[0]);
    BORD[1] = build_perm_base(1, BTAB[1]);
}

/* Direct product of a base group (index which) with Z_k: element x*k + c. */
static int set_product(int which, int k) {
    int o = BORD[which];
    if (o <= 0) return 0;
    N = o * k;
    if (N > MAXG) return 0;
    const int *bt = BTAB[which];
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = bt[x * o + y] * k + (c + e) % k;
    finish_group();
    return 1;
}

static GDesc descs[MAXDESC];

static int enumerate_groups(int M) {
    int cnt = 0;
    for (int m = 1; m <= M && cnt < MAXDESC; m++) {
        if (M % m) continue;
        int k = M / m;
        if (m == 1) {
            descs[cnt].kind = 0; descs[cnt].m = 1; descs[cnt].k = k; descs[cnt].r = 0;
            cnt++;
            continue;
        }
        for (int r = 1; r < m && cnt < MAXDESC; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            descs[cnt].kind = 0; descs[cnt].m = m; descs[cnt].k = k; descs[cnt].r = r;
            cnt++;
        }
    }
    for (int w = 0; w < 2 && cnt < MAXDESC; w++) {
        int o = BORD[w];
        if (o > 0 && M % o == 0 && M / o >= 1) {
            descs[cnt].kind = 1 + w; descs[cnt].m = 0; descs[cnt].k = M / o; descs[cnt].r = 0;
            cnt++;
        }
    }
    return cnt;
}

static void apply_desc(const GDesc *g) {
    if (g->kind == 0) set_semidirect(g->m, g->k, g->r);
    else set_product(g->kind - 1, g->k);
}

/* ---------------------------------------------------------------- bi-Cayley search */
static int S[MAXD], bestS[MAXD];
static int distv[MAXV], qv[MAXV];

static long cost_from(int src) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) distv[v] = -1;
    int head = 0, tail = 0;
    distv[src] = 0;
    qv[tail++] = src;
    while (head < tail) {
        int v = qv[head++];
        int dv = distv[v] + 1;
        if (v < N) {
            for (int i = 0; i < d; i++) {
                int u = N + GT[v * N + S[i]];
                if (distv[u] < 0) {
                    distv[u] = dv;
                    qv[tail++] = u;
                }
            }
        } else {
            int y = v - N;
            for (int i = 0; i < d; i++) {
                int u = GT[y * N + INV[S[i]]];
                if (distv[u] < 0) {
                    distv[u] = dv;
                    qv[tail++] = u;
                }
            }
        }
    }
    long c = 0;
    for (int v = 0; v < V; v++) {
        if (distv[v] < 0) c += 2;
        else if (distv[v] > D) c += distv[v] - D;
    }
    return c;
}

static long cost_total(void) { return cost_from(0) + cost_from(N); }

static int in_prefix(int g, int k) {
    for (int i = 0; i < k; i++)
        if (S[i] == g) return 1;
    return 0;
}

static int sa_group(double until) {
    for (int i = 0; i < d; i++) {
        int g;
        do g = rndint(N); while (in_prefix(g, i));
        S[i] = g;
    }
    long cur = cost_total(), best = cur;
    memcpy(bestS, S, sizeof(S));
    double T0 = 3.0, T = T0;
    long stall = 0;
    for (long it = 0; best > 0; it++) {
        if ((it & 63) == 0 && now() > until) break;
        int i = rndint(d);
        int g;
        do g = rndint(N); while (in_prefix(g, d));
        int old = S[i];
        S[i] = g;
        long nv = cost_total();
        long delta = nv - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nv;
        else S[i] = old;
        if (cur < best) {
            best = cur;
            memcpy(bestS, S, sizeof(S));
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.9995;
        if (T < 0.2) T = 0.2;
        if (stall > 20000) {
            memcpy(S, bestS, sizeof(S));
            cur = best;
            T = T0;
            stall = 0;
        }
    }
    memcpy(S, bestS, sizeof(S));
    return best == 0;
}

static void graph_from_S(Graph *g) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= N);
    }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++) add_edge(g, x, N + GT[x * N + S[i]]);
}

static void search(Graph *best) {
    static Graph cand;
    static const int special[4] = {336, 504, 672, 1008};
    long moore = moore_bound();
    while (now() < t_stop) {
        int lo = best->n / 2 + 1;
        if (2L * lo > moore || 2 * lo > MAXN || lo > MAXG) break;
        int M = lo + rndint(40);
        if (rndint(4) == 0) {
            int s = special[rndint(4)];
            if (s >= lo) M = s;
        }
        if (2L * M > moore || 2 * M > MAXN || M > MAXG) M = lo;
        int cnt = enumerate_groups(M);
        if (cnt == 0) continue;
        GDesc g = descs[rndint(cnt)];
        apply_desc(&g);
        if (N != M) continue;
        double until = now() + 2.0;
        if (until > t_stop) until = t_stop;
        if (sa_group(until)) {
            graph_from_S(&cand);
            if (cand.n > best->n && is_valid(&cand)) *best = cand;
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
    t_stop = t0 + limit * 0.9;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    if (D < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (d >= 3 && best.n < moore_bound()) {
        init_perm_bases();
        search(&best);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): degree 4, diameter 6, 728 vertices.

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
    """Algebraic candidates that are valid for diameter D (may be empty)."""
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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d < 3 or d > 16 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except Exception:
        pass
    return best
