"""Cayley-type bipartite lift search, for the weakest target (d=4, D=9).

Changed approach: instead of growing a small algebraic start by annealing, the C engine searches
voltage lifts over the nonabelian groups PSL(2,q) and PGL(2,q) (q prime). With base multigraph
p = 1 or 2 per side, the lift has 2*p*|G| vertices and is vertex-transitive on each fibre under
left multiplication. So the diameter test needs only 2p BFS runs from fibre representatives. Random
voltages in a large nonabelian group give near-random-graph expansion, which is what diameter 9 needs.
Candidates are tried in increasing order of size, and the largest valid lift found is returned.
Python keeps the algebraic start (PG(2,q), W(q), K_{d,d}) as the fallback and validates every output.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: voltage lifts over PSL(2,q) / PGL(2,q), q prime.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Lift: base multigraph on p + p vertices, d-regular, voltages in G. A-fibre i, element x -> i*N + x;
 * B-fibre j, element y -> (p+j)*N + y. Dart (i, j, g) joins (A_i, x) to (B_j, x*g).
 * Left multiplication by G is an automorphism, so distances from (a, x) reduce to distances from
 * (a, e). The objective counts (fibre representative, vertex) pairs beyond distance D.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 12288
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 2
#define MAXDART (MAXD * MAXP)
#define PATIENCE 4000

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
static int badv[MAXN];

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

/* ------------------------------------------------------------------ groups PSL/PGL(2,q) */

typedef struct {
    int q, type, N;   /* type 1 = PSL(2,q), type 2 = PGL(2,q); element 0 is the identity */
    int *mat;         /* 4 entries per element: a b c e  = [[a b],[c e]] */
    int *index;       /* q^4 entries: encoded normalized matrix -> element index or -1 */
    int *invt;        /* inverses mod q */
} Group;

static int md(long x, int q) {
    x %= q;
    if (x < 0) x += q;
    return (int)x;
}

static void normalize4(int *m, int q, const int *invt) {
    int k = 0;
    while (k < 4 && m[k] == 0) k++;
    if (k == 4) return;
    int c = invt[m[k]];
    for (int i = 0; i < 4; i++) m[i] = (int)((long)m[i] * c % q);
}

static long encode4(const int *m, int q) {
    return (((long)m[0] * q + m[1]) * q + m[2]) * q + m[3];
}

static int build_group(Group *G, int q, int type) {
    G->q = q;
    G->type = type;
    G->N = 0;
    long q4 = (long)q * q * q * q;
    G->index = malloc(sizeof(int) * (size_t)q4);
    G->invt = malloc(sizeof(int) * (size_t)q);
    G->mat = malloc(sizeof(int) * 4 * (size_t)q4);
    if (!G->index || !G->invt || !G->mat) return 0;
    for (long e = 0; e < q4; e++) G->index[e] = -1;
    G->invt[0] = 0;
    for (int x = 1; x < q; x++) G->invt[x] = (int)powmod(x, q - 2, q);
    int id[4] = {1, 0, 0, 1};
    memcpy(G->mat, id, sizeof id);
    G->index[encode4(id, q)] = 0;
    int cnt = 1;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    int m[4] = {a, b, c, e};
                    int det = md((long)a * e - (long)b * c, q);
                    if (det == 0) continue;
                    int k = 0;
                    while (k < 4 && m[k] == 0) k++;
                    if (m[k] != 1) continue;   /* projective normal form */
                    if (type == 1 && powmod(det, (q - 1) / 2, q) != 1) continue;
                    long code = encode4(m, q);
                    if (G->index[code] != -1) continue;
                    memcpy(G->mat + 4 * cnt, m, sizeof m);
                    G->index[code] = cnt++;
                }
    G->N = cnt;
    return 1;
}

static void free_group(Group *G) {
    free(G->mat);
    free(G->index);
    free(G->invt);
    G->mat = NULL;
    G->index = NULL;
    G->invt = NULL;
}

static int gmul(const Group *G, int x, int y) {
    int q = G->q;
    const int *A = G->mat + 4 * x, *B = G->mat + 4 * y;
    int m[4];
    m[0] = (int)(((long)A[0] * B[0] + (long)A[1] * B[2]) % q);
    m[1] = (int)(((long)A[0] * B[1] + (long)A[1] * B[3]) % q);
    m[2] = (int)(((long)A[2] * B[0] + (long)A[3] * B[2]) % q);
    m[3] = (int)(((long)A[2] * B[1] + (long)A[3] * B[3]) % q);
    normalize4(m, q, G->invt);
    return G->index[encode4(m, q)];
}

static int ginv(const Group *G, int x) {
    int q = G->q;
    const int *A = G->mat + 4 * x;
    int m[4] = {A[3], md(-(long)A[1], q), md(-(long)A[2], q), A[0]};
    normalize4(m, q, G->invt);
    return G->index[encode4(m, q)];
}

/* ------------------------------------------------------------------ voltage lifts */

static int nd;
static int dart_i[MAXDART], dart_j[MAXDART], dart_g[MAXDART];
static int Aset[MAXP][MAXD], Bset[MAXP][MAXD];
static int RT[MAXDART][MAXN];   /* RT[t][x] = x * g_t */
static int LT[MAXDART][MAXN];   /* LT[t][y] = y * g_t^{-1} */

static int base_connected(int M[MAXP][MAXP], int p) {
    int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, cnt = 1;
    seen[0] = 1;
    stack[top++] = 0;
    while (top) {
        int v = stack[--top];
        for (int u = 0; u < 2 * p; u++) {
            if (seen[u]) continue;
            int linked = v < p ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
            if (linked) {
                seen[u] = 1;
                cnt++;
                stack[top++] = u;
            }
        }
    }
    return cnt == 2 * p;
}

/* Voltage for dart t, distinct from the other darts on the same (i, j) pair. */
static int fresh_voltage(int t, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int s = 0; s < nd; s++)
            if (s != t && dart_i[s] == dart_i[t] && dart_j[s] == dart_j[t] && dart_g[s] == g) {
                clash = 1;
                break;
            }
        if (!clash) return g;
    }
}

static void set_tables(const Group *G, int t) {
    int N = G->N, g = dart_g[t], gi = ginv(G, g);
    for (int x = 0; x < N; x++) {
        RT[t][x] = gmul(G, x, g);
        LT[t][x] = gmul(G, x, gi);
    }
}

/* Random d-regular base multigraph on p + p vertices, connected; then random distinct voltages. */
static void init_lift(const Group *G, int p) {
    int M[MAXP][MAXP];
    for (;;) {
        memset(M, 0, sizeof M);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) M[i][perm[i]]++;
        }
        if (base_connected(M, p)) break;
    }
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dart_i[nd] = i;
                dart_j[nd] = j;
                dart_g[nd] = -1;
                nd++;
            }
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        Aset[dart_i[t]][ca[dart_i[t]]++] = t;
        Bset[dart_j[t]][cb[dart_j[t]]++] = t;
    }
    for (int t = 0; t < nd; t++) dart_g[t] = fresh_voltage(t, G->N);
    for (int t = 0; t < nd; t++) set_tables(G, t);
}

static int vis[MAXN];
static int vstamp = 0;
static int bq[MAXN];

/* Sum over the 2p fibre representatives of the number of vertices at distance > D. */
static long orbit_bad(int p, int N) {
    int nv = 2 * p * N, pN = p * N;
    long bad = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        vstamp++;
        int head = 0, tail = 0;
        vis[src] = vstamp;
        bq[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int v = bq[head++];
                if (v < pN) {
                    int i = v / N, x = v - i * N;
                    for (int k = 0; k < d; k++) {
                        int t = Aset[i][k];
                        int u = (p + dart_j[t]) * N + RT[t][x];
                        if (vis[u] != vstamp) {
                            vis[u] = vstamp;
                            bq[tail++] = u;
                        }
                    }
                } else {
                    int w = v - pN;
                    int j = w / N, y = w - j * N;
                    for (int k = 0; k < d; k++) {
                        int t = Bset[j][k];
                        int u = dart_i[t] * N + LT[t][y];
                        if (vis[u] != vstamp) {
                            vis[u] = vstamp;
                            bq[tail++] = u;
                        }
                    }
                }
            }
        }
        bad += nv - tail;
    }
    return bad;
}

static void build_graph(Graph *g, int p, int N) {
    int pN = p * N;
    g->n = 2 * pN;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = v >= pN;
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dart_i[t] * N + x, pN + dart_j[t] * N + RT[t][x]);
}

/* Random restarts plus annealing-style hill climbing on the voltages, until time 'until'. */
static int search_lift(const Group *G, int p, double until, Graph *out) {
    int N = G->N;
    long it = 0;
    while (now() < until) {
        init_lift(G, p);
        long bad = orbit_bad(p, N);
        int stall = 0;
        while (bad > 0 && stall < PATIENCE) {
            if ((++it & 127) == 0 && now() > until) break;
            int t = rndint(nd);
            int old = dart_g[t];
            dart_g[t] = fresh_voltage(t, N);
            set_tables(G, t);
            long nb = orbit_bad(p, N);
            if (nb < bad) {
                bad = nb;
                stall = 0;
            } else if (nb == bad || rnd01() < 0.01) {
                bad = nb;
                stall++;
            } else {
                dart_g[t] = old;
                set_tables(G, t);
                stall++;
            }
        }
        if (bad == 0) {
            build_graph(out, p, N);
            if (is_valid(out)) return 1;
        }
    }
    return 0;
}

/* ------------------------------------------------------------------ main */

typedef struct { int q, type, p, M; } Cand;

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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, cand;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    long moore = moore_bound();

    if (D >= 2 && best.n < moore) {
        Cand cands[64];
        int nc = 0;
        static const int qs[] = {5, 7, 11, 13, 17, 19, 23};
        for (int qi = 0; qi < 7; qi++) {
            long q = qs[qi];
            long pgl = q * (q * q - 1);
            for (int type = 1; type <= 2; type++)
                for (int p = 1; p <= 2; p++) {
                    long N = type == 1 ? pgl / 2 : pgl;
                    long M = 2L * p * N;
                    if (M <= best.n || M > moore || M > MAXN || N < d) continue;
                    if (nc < 64) {
                        cands[nc].q = (int)q;
                        cands[nc].type = type;
                        cands[nc].p = p;
                        cands[nc].M = (int)M;
                        nc++;
                    }
                }
        }
        for (int i = 1; i < nc; i++) {
            Cand key = cands[i];
            int j = i - 1;
            while (j >= 0 && cands[j].M > key.M) {
                cands[j + 1] = cands[j];
                j--;
            }
            cands[j + 1] = key;
        }
        for (int c = 0; c < nc; c++) {
            if (cands[c].M <= best.n) continue;
            double rem = t_end - now();
            if (rem < 0.3) break;
            int left = 0;
            for (int c2 = c; c2 < nc; c2++)
                if (cands[c2].M > best.n) left++;
            double slice = rem / left * 1.6;
            if (slice > rem) slice = rem;
            Group G;
            if (!build_group(&G, cands[c].q, cands[c].type)) {
                free_group(&G);
                continue;
            }
            long M2 = 2L * cands[c].p * G.N;
            if (M2 > best.n && M2 <= MAXN &&
                search_lift(&G, cands[c].p, now() + slice, &cand)) {
                if (cand.n > best.n) copy_graph(&best, &cand);
            }
            free_group(&G);
        }
    }

    if (best.n == 0) complete_bipartite(&best);
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = min(0.8 * time_limit, time_limit - 6.0) - (time.monotonic() - t0)
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 6.0)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
