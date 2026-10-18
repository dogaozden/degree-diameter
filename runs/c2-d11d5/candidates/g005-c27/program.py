"""Bold revision: a C bi-Cayley annealer over semidirect-product lifts, then the C grow-by-two engine.

Stage 0: exact constructions (projective plane, Araujo-Pardo-Lopez, W(q)) where they apply.
Stage 1 (new): C simulated annealing over d-regular bipartite lifts of k+k base vertices with
    voltages in Z_m x| Z_k2. Reachability is checked exactly: by left-translation symmetry, only
    the 2k identity vertices need BFS, so the cost is exact and cheap.
Stage 2: C grow-by-two engine (from the previous version) starting from the best graph so far.
Fallback: K_{d,d}, which is valid for D >= 2. Every returned graph passes lib.is_valid.
"""
import itertools
import time

import lib


C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXKB 8
#define MAXL 32
#define MAXV 12000
#define PEN 1000L

static int d, D;
static uint64_t rs = 0x2545F4914F6CDD1DULL;
static double t_end;

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

/* Group Z_MM x| Z_K2, element (a,b) coded as a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int KB, K2, MM, RR, GG, NN;
static int powr[64];

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

static int gcdi(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static void set_group(int kb, int k2, int mm, int rr) {
    KB = kb;
    K2 = k2;
    MM = mm;
    RR = rr;
    GG = mm * k2;
    NN = 2 * kb * GG;
    powr[0] = 1 % mm;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long)powr[b - 1] * rr % mm);
}

static int gmul(int x, int y) {
    int a1 = x / K2, b1 = x % K2, a2 = y / K2, b2 = y % K2;
    return ((a1 + powr[b1] * a2) % MM) * K2 + (b1 + b2) % K2;
}

static int ginv(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    int c = (MM - (int)((long)powr[nb] * a % MM)) % MM;
    return c * K2 + nb;
}

/* Darts: layer l maps A-block i to B-block P[l][i] with voltage S[l][i].
 * Vertex A_{i,g} = i*GG+g, B_{j,h} = (KB+j)*GG+h.  A_{i,g} ~ B_{j,g*s}. */
static int P[MAXL][MAXKB], S[MAXL][MAXKB];
static int adj[MAXV][MAXL];
static int vis[MAXV], qb[MAXV];
static int stampc = 0;

static int bP[MAXL][MAXKB], bS[MAXL][MAXKB];
static int bKB, bK2, bMM, bRR;
static int bestN = 0;

static void set_dart(int l, int i) {
    int j = P[l][i], s = S[l][i], si = ginv(s);
    int bb = (KB + j) * GG;
    for (int g = 0; g < GG; g++) adj[i * GG + g][l] = bb + gmul(g, s);
    for (int h = 0; h < GG; h++) adj[bb + h][l] = i * GG + gmul(h, si);
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < KB; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = 0; l2 < l1; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static int bfs_count(int src) {
    int head = 0, tail = 0;
    stampc++;
    qb[tail++] = src;
    vis[src] = stampc;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qb[head++];
            for (int l = 0; l < d; l++) {
                int u = adj[v][l];
                if (vis[u] != stampc) {
                    vis[u] = stampc;
                    qb[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Exact by left-translation symmetry: only the 2*KB identity vertices need BFS. */
static long full_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * KB; b++) c += NN - bfs_count(b * GG);
    return c;
}

static long total_cost(void) { return full_cost() + PEN * dupcount(); }

static void random_config(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < KB; i++) P[l][i] = i;
        for (int i = KB - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < KB; i++) S[l][i] = rndint(GG);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) set_dart(l, i);
}

static int sa_run(int iters, int patience) {
    random_config();
    long cost = total_cost();
    long bestc = cost;
    int last = 0;
    double c0 = cost > 0 ? (double)cost : 1.0;
    for (int t = 0; t < iters; t++) {
        if (cost == 0) return 1;
        if ((t & 63) == 0 && now() > t_end) break;
        if (t - last > patience) break;
        double temp = 0.5 + 0.02 * c0 * (1.0 - (double)t / iters);
        int l = rndint(d);
        if (KB >= 2 && rnd01() < 0.3) {
            int i1 = rndint(KB), i2 = rndint(KB - 1);
            if (i2 >= i1) i2++;
            int tmp = P[l][i1];
            P[l][i1] = P[l][i2];
            P[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long nc = total_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                tmp = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
        } else {
            int i = rndint(KB);
            int old = S[l][i];
            int nw = rndint(GG);
            if (nw == old) continue;
            S[l][i] = nw;
            set_dart(l, i);
            long nc = total_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / temp)) {
                cost = nc;
            } else {
                S[l][i] = old;
                set_dart(l, i);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            last = t;
        }
    }
    return cost == 0;
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
    t_end = t0 + limit * 0.9 - 0.3;
    rs ^= (uint64_t)(seed + 7) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXL || D < 2) {
        printf("0 0\n");
        return 0;
    }

    while (now() < t_end) {
        int kc = 1 + rndint(6);
        int minG = bestN / (2 * kc) + 1;
        int lo = (d + kc - 1) / kc + 1;
        if (minG < lo) minG = lo;
        int Gt = minG + rndint(1 + minG / 25);
        static const int K2S[13] = {1, 2, 2, 3, 4, 4, 5, 6, 6, 8, 9, 10, 12};
        int k2c = K2S[rndint(13)];
        int mc = (Gt + k2c - 1) / k2c;
        if (mc < 2) mc = 2;
        int rc = -1;
        if (k2c == 1) {
            rc = 1 % mc;
        } else {
            int start = rndint(mc - 1);
            for (int t = 0; t < mc - 1; t++) {
                int cand = 1 + (start + t) % (mc - 1);
                if (gcdi(cand, mc) != 1) continue;
                if (powmod(cand, k2c, mc) != 1 % mc) continue;
                rc = cand;
                break;
            }
        }
        if (rc < 0) continue;
        set_group(kc, k2c, mc, rc);
        if (NN > MAXV || NN <= bestN) continue;
        if (sa_run(4000, 1000)) {
            bestN = NN;
            bKB = KB;
            bK2 = K2;
            bMM = MM;
            bRR = RR;
            memcpy(bP, P, sizeof P);
            memcpy(bS, S, sizeof S);
        }
    }

    if (bestN <= 0) {
        printf("0 0\n");
        return 0;
    }
    set_group(bKB, bK2, bMM, bRR);
    memcpy(P, bP, sizeof P);
    memcpy(S, bS, sizeof S);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < KB; i++) set_dart(l, i);
    if (total_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    int A = KB * GG;
    printf("%d %d\n", NN, A * d);
    for (int v = 0; v < A; v++)
        for (int l = 0; l < d; l++) printf("%d %d\n", v, adj[v][l]);
    return 0;
}
'''


C_GROW = r'''
/* Grow-by-two search core.
 * Usage:  prog d D seed time_limit < start_graph
 * stdin:  "n m" + m edge lines (valid bipartite start), or "0 0".
 * stdout: "n m" + edges of the best valid graph found (never worse than the input).
 *
 * Each step samples several candidate insertions of one vertex on each side (using the
 * spare degree freed by d-1 deleted edges), keeps the one with the fewest bad pairs,
 * then anneals degree-preserving edge swaps until every pair is within distance D.
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
#define CANDS 6

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static uint64_t rng_state = 88172645463325252ULL;
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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

/* Number of unordered pairs at distance > D; also sets badv[v]. */
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

static double t_end;
static Graph gbest, gwork, gtry;
static int used[MAXN];
static int stamp = 0;

/* Build one candidate: insert x (side 0) and y (side 1) joined by an edge, and steal
 * d-1 disjoint edges a-b (a on side 0, b on side 1) to give x and y their degree. */
static void make_candidate(const Graph *best, Graph *w) {
    int n = best->n;
    copy_graph(w, best);
    int x = n, y = n + 1;
    w->n = n + 2;
    w->deg[x] = w->deg[y] = 0;
    w->side[x] = 0;
    w->side[y] = 1;
    add_edge(w, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (w->side[a] != 0 || used[a] == stamp || w->deg[a] == 0) continue;
        int b = w->adj[a][rndint(w->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(w, a, b);
        add_edge(w, x, b);
        add_edge(w, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
}

/* Try several random candidate insertions and keep the one with the fewest bad pairs. */
static void choose_candidate(const Graph *best, Graph *work) {
    long bestbad = -1;
    for (int c = 0; c < CANDS; c++) {
        make_candidate(best, &gtry);
        long b = bad_pairs(&gtry);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &gtry);
        }
        if (b == 0) break;
    }
}

/* One grow-by-two attempt starting from best; on success work holds n+2 valid vertices. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    choose_candidate(best, work);
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v = rndint(work->n);
        for (int tries = 0; tries < 30 && badv[v] == 0; tries++) v = rndint(work->n);
        if (work->deg[v] == 0) continue;
        int u = work->adj[v][rndint(work->deg[v])];
        int s = rndint(work->n);
        if (work->side[s] != work->side[v] || s == v || work->deg[s] == 0) continue;
        int t = work->adj[s][rndint(work->deg[s])];
        if (t == u || has_edge(work, v, t) || has_edge(work, s, u)) continue;
        del_edge(work, v, u);
        del_edge(work, s, t);
        add_edge(work, v, t);
        add_edge(work, s, u);
        long nb = bad_pairs(work);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

static void grow_search(double until) {
    while (now() < until && gbest.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&gbest, &gwork, now() + slice)) copy_graph(&gbest, &gwork);
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
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&gbest);
    if (gbest.n == 0) { printf("0 0\n"); return 0; }
    grow_search(t_end);
    if (!is_valid(&gbest)) { printf("0 0\n"); return 0; }
    print_graph(&gbest);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    total = max(2.0, 0.85 * time_limit - 2.0)
    final = t0 + total

    # Exact constructions (calibration-style cases return immediately).
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Stage 1: bi-Cayley annealer in C (exact orbit-based reachability check).
    remaining = final - time.monotonic()
    if remaining > 4.0:
        b1 = round(0.55 * remaining, 2)
        try:
            text = lib.run_c(C_LIFT, [d, D, seed, b1], stdin_graph=None, timeout=b1 + 15.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    # Stage 2: grow-by-two from the best graph found so far.
    remaining = final - time.monotonic() - 1.0
    if remaining > 2.0 and best_n <= 8000:
        try:
            text = lib.run_c(C_GROW, [d, D, seed, round(remaining, 2)],
                             stdin_graph=best, timeout=remaining + 15.0)
            consider(*lib.parse_graph_text(text))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
