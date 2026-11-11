"""Combined program, bold variant. Python builds the best algebraic start (K_{d,d}, PG(2,q),
Araujo-Pardo-Lopez, W(q), or H(q) for d = 3, 5), checks it with lib.is_valid, and then runs two
C searches with fallback. Stage 1 (new): bi-Cayley (Haar-type) graphs over affine groups
F_q x| H (H <= F_q^*, non-abelian), searched by annealing over the connection set S, with
orbit-reduced diameter checks from the two fibre roots. Stage 2 (parent): voltage-lift search and
grow-by-two annealing from the best graph so far. Every output is checked with lib.is_valid and
the larger graph is kept only if it is valid."""
import itertools
import time

import numpy as np

import lib

AFFINE_C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley search over affine groups G = F_q x| H, H <= F_q^* cyclic of order k.
 * Element i*q + b represents x -> h^i x + b. Graph: A-vertex x adjacent to B-vertex N + x*s
 * for each s in S, |S| = d. Left multiplication is an automorphism that is transitive on each
 * side, so diameter <= D holds iff BFS from A-root 0 and B-root N reaches everything in D steps.
 * Usage: prog d D seed budget minN maxN ; stdout "n m" + edges, or "0 0".
 */
#define MAXN 2048
#define MAXV (2 * MAXN)
#define MAXDEG 32
#define MAXCAND 200000

typedef struct { int N, q, k; } Cand;

static int d, D, K, Q, N;
static int pw[MAXN + 1];
static int S[MAXDEG], Sinv[MAXDEG];
static int Rt[MAXDEG][MAXN], Lt[MAXDEG][MAXN];
static int dist[MAXV], qbuf[MAXV];
static double t_end;
static Cand cands[MAXCAND];
static int nc;

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

static int is_prime(int q) {
    if (q < 2) return 0;
    for (int p = 2; p * p <= q; p++)
        if (q % p == 0) return 0;
    return 1;
}

static int prim_root(int q) {
    int fac[32], nf = 0, m = q - 1;
    for (int p = 2; p * p <= m; p++)
        if (m % p == 0) {
            fac[nf++] = p;
            while (m % p == 0) m /= p;
        }
    if (m > 1) fac[nf++] = m;
    for (int g = 2; g < q; g++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (powmod(g, (q - 1) / fac[i], q) == 1) ok = 0;
        if (ok) return g;
    }
    return 1;
}

static void set_group(int q, int k) {
    Q = q;
    K = k;
    N = q * k;
    int g = prim_root(q);
    int h = (int)powmod(g, (q - 1) / k, q);
    pw[0] = 1 % q;
    for (int i = 1; i < k; i++) pw[i] = (int)((long)pw[i - 1] * h % q);
}

static int amul(int x, int y) {
    int i1 = x / Q, b1 = x % Q, i2 = y / Q, b2 = y % Q;
    int i = i1 + i2;
    if (i >= K) i -= K;
    int b = (int)(((long)pw[i1] * b2 + b1) % Q);
    return i * Q + b;
}

static int ainv(int x) {
    int i1 = x / Q, b1 = x % Q;
    int ni = (K - i1) % K;
    int nb = (int)((Q - ((long)pw[ni] * b1) % Q) % Q);
    return ni * Q + nb;
}

static void set_col(int t) {
    for (int x = 0; x < N; x++) {
        Rt[t][x] = amul(x, S[t]);
        Lt[t][x] = amul(x, Sinv[t]);
    }
}

static int in_S(int e, int upto) {
    for (int t = 0; t < upto; t++)
        if (S[t] == e) return 1;
    return 0;
}

static void random_S(void) {
    for (int t = 0; t < d; t++) {
        int e;
        do e = rndint(N); while (in_S(e, t));
        S[t] = e;
        Sinv[t] = ainv(e);
    }
    for (int t = 0; t < d; t++) set_col(t);
}

static int reach(int root) {
    int V = 2 * N;
    for (int v = 0; v < V; v++) dist[v] = -1;
    int head = 0, tail = 0;
    dist[root] = 0;
    qbuf[tail++] = root;
    while (head < tail) {
        int v = qbuf[head++];
        if (dist[v] >= D) continue;
        for (int t = 0; t < d; t++) {
            int u = v < N ? N + Rt[t][v] : Lt[t][v - N];
            if (dist[u] < 0) {
                dist[u] = dist[v] + 1;
                qbuf[tail++] = u;
            }
        }
    }
    return tail;
}

static long cost(void) {
    return (long)(2 * N - reach(0)) + (long)(2 * N - reach(N));
}

static int anneal(double until) {
    random_S();
    long cur = cost();
    long best_c = cur, since = 0;
    const double T = 0.5;
    for (long it = 0; cur > 0; it++) {
        if ((it & 127) == 0 && now() > until) return 0;
        int t = rndint(d);
        int old = S[t], oldinv = Sinv[t];
        int e;
        do e = rndint(N); while (in_S(e, d));
        S[t] = e;
        Sinv[t] = ainv(e);
        set_col(t);
        long c = cost();
        if (c <= cur || rnd01() < exp((double)(cur - c) / T)) {
            cur = c;
        } else {
            S[t] = old;
            Sinv[t] = oldinv;
            set_col(t);
        }
        if (cur < best_c) {
            best_c = cur;
            since = 0;
        } else if (++since > 60000) {
            random_S();
            cur = cost();
            best_c = cur;
            since = 0;
        }
    }
    return 1;
}

/* Full explicit check: degrees, no multi-edges, and BFS from every vertex within D. */
static int validate(void) {
    static int adj[MAXV][MAXDEG];
    static int deg[MAXV];
    int V = 2 * N;
    for (int v = 0; v < V; v++) deg[v] = 0;
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++) {
            int y = N + Rt[t][x];
            if (deg[x] >= MAXDEG || deg[y] >= MAXDEG) return 0;
            adj[x][deg[x]++] = y;
            adj[y][deg[y]++] = x;
        }
    for (int v = 0; v < V; v++) {
        if (deg[v] != d) return 0;
        for (int i = 0; i < deg[v]; i++)
            for (int j = 0; j < i; j++)
                if (adj[v][i] == adj[v][j]) return 0;
    }
    for (int s = 0; s < V; s++) {
        for (int v = 0; v < V; v++) dist[v] = -1;
        int head = 0, tail = 0;
        dist[s] = 0;
        qbuf[tail++] = s;
        while (head < tail) {
            int v = qbuf[head++];
            if (dist[v] >= D) continue;
            for (int i = 0; i < deg[v]; i++) {
                int u = adj[v][i];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    qbuf[tail++] = u;
                }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

static void print_graph(void) {
    printf("%d %d\n", 2 * N, N * d);
    for (int x = 0; x < N; x++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", x, N + Rt[t][x]);
}

static int cmp_desc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->N != y->N) return y->N - x->N;
    return x->q - y->q;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed budget minN maxN\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double budget = atof(argv[4]);
    int minN = atoi(argv[5]);
    int maxN = atoi(argv[6]);
    if (maxN > MAXN) maxN = MAXN;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    t_end = t0 + budget * 0.92;
    if (d < 1 || d > MAXDEG || D < 1 || maxN < minN) {
        printf("0 0\n");
        return 0;
    }

    nc = 0;
    for (int q = 3; q <= maxN; q++) {
        if (!is_prime(q)) continue;
        for (int k = 2; k <= q - 1; k++) {
            if ((q - 1) % k) continue;
            long Nn = (long)q * k;
            if (Nn < minN || Nn > maxN || Nn <= d) continue;
            if (nc < MAXCAND) {
                cands[nc].N = (int)Nn;
                cands[nc].q = q;
                cands[nc].k = k;
                nc++;
            }
        }
    }
    qsort(cands, nc, sizeof(Cand), cmp_desc);

    for (int i = 0; i < nc; i++) {
        double left = t_end - now();
        if (left < 0.3) break;
        double slice = left * 0.3;
        if (slice < 2.0) slice = left;
        set_group(cands[i].q, cands[i].k);
        if (anneal(now() + slice) && validate()) {
            print_graph();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''

OLD_C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a known-valid starting graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Voltage lifts over groups Z_m x|_r Z_k with base multigraphs on p <= 4 vertices per side.
 *    The diameter objective is orbit-reduced: the group acts regularly on each fibre, so only
 *    BFS from the 2p fibre representatives is needed.
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving edge swaps.
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
#define MAXP 4

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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

static int random_group(int N, Grp *G) {
    long count = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                G->m = m; G->k = k; G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
    return 1;
}

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) { int j = rndint(i + 1); int s = perm[i]; perm[i] = perm[j]; perm[j] = s; }
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
static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective. Left multiplication by the group is an automorphism of
 * every lift, and it is transitive on each fibre, so distances from all vertices are covered
 * by BFS from the 2p fibre representatives (element 0 of each fibre). Returns the number of
 * (representative, vertex) pairs at distance > D; zero means diameter <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

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

/* Hill-climb the voltages of one random base multigraph over the group G. */
static int lift_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, G, dt, nd);
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

/* Search lifts of order strictly larger than the current best. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore || target > MAXN) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2L * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        if (lift_try(&cand, p, N, &G, 20000, until) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* Insert one new vertex per side into a copy of best, then anneal edge swaps until valid. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXN];
    static int stamp = 0;
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0, tries = 0; k < d - 1 && tries < 100000; tries++) {
        int a = rndint(n);
        if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
        int b = work->adj[a][rndint(work->deg[a])];
        if (used[b] == stamp || b >= n) continue;
        del_edge(work, a, b);
        add_edge(work, x, b);
        add_edge(work, y, a);
        used[a] = used[b] = stamp;
        k++;
    }
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

static void grow_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
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
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    int had_start = best.n > 0;

    if (D >= 2 && best.n < moore_bound()) {
        double share = had_start ? 0.5 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * share);
        if (best.n > 0) grow_search(&best, t_end);
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


def _gh_h(q):
    """Incidence graph of the split Cayley hexagon H(q), q in {2, 4}: degree q+1, diameter 6.

    Characteristic 2, so signs vanish. Points: projective points of X0X4 + X1X5 + X2X6 + X3^2 = 0
    in PG(6, q). Lines: lines of that quadric whose Plucker coordinates p_kl satisfy
    p12 = p34, p45 = p23, p02 = p35, p56 = p03, p01 = p36, p46 = p13.
    Order 2(q^6-1)/(q-1). The caller checks validity with lib.is_valid, so a mistake here
    only costs the candidate, never the output."""
    F = lib.GF(q)
    mt, at = F.mul_table, F.add_table

    def Q(v):
        s = F.add(F.mul(v[0], v[4]), F.mul(v[1], v[5]))
        s = F.add(s, F.mul(v[2], v[6]))
        return F.add(s, F.mul(v[3], v[3]))

    pts = [v for v in itertools.product(range(q), repeat=7)
           if any(v) and next(c for c in v if c) == 1 and Q(v) == 0]
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    I, J = np.triu_indices(N, 1)

    # Collinearity on the quadric: polar form B(x, y) = x0y4+x4y0 + x1y5+x5y1 + x2y6+x6y2 = 0.
    B = np.zeros(I.shape, dtype=np.int64)
    for a, b in ((0, 4), (1, 5), (2, 6)):
        B = at[B, mt[P[I, a], P[J, b]]]
        B = at[B, mt[P[I, b], P[J, a]]]
    keep = B == 0
    I, J = I[keep], J[keep]

    def pl(k, l):
        return at[mt[P[I, k], P[J, l]], mt[P[I, l], P[J, k]]]

    ok = ((pl(1, 2) == pl(3, 4)) & (pl(4, 5) == pl(2, 3)) & (pl(0, 2) == pl(3, 5))
          & (pl(5, 6) == pl(0, 3)) & (pl(0, 1) == pl(3, 6)) & (pl(4, 6) == pl(1, 3)))

    lines = set()
    for i, j in zip(I[ok].tolist(), J[ok].tolist()):
        x, y = pts[i], pts[j]
        L = {i}
        for t in range(q):
            v = [F.add(F.mul(t, x[k]), y[k]) for k in range(7)]
            c = next(c for c in v if c)
            ic = F.inv(c)
            L.add(index[tuple(F.mul(ic, a) for a in v)])
        lines.add(frozenset(L))

    lines = sorted(sorted(L) for L in lines)
    edges = []
    for li, L in enumerate(lines):
        for p in L:
            edges.append((p, N + li))
    return N + len(lines), edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty). Each is checked by the caller."""
    builders = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        builders.append(lambda: lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        builders.append(lambda: lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            builders.append(lambda q=q: _gq_w(q))
    if D >= 6 and d - 1 in (2, 4):
        builders.append(lambda q=d - 1: _gh_h(q))
    out = []
    for make in builders:
        try:
            out.append(make())
        except Exception:
            pass
    return out


def _affine_bicayley(d, D, seed, budget, minN, maxN):
    """Run the affine bi-Cayley search in C; returns (n, edges) or (0, []) when nothing was found."""
    text = lib.run_c(AFFINE_C_SOURCE, [d, D, seed, budget, minN, maxN],
                     stdin_graph=None, timeout=budget + 5)
    return lib.parse_graph_text(text)


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
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    deadline = t0 + 0.88 * time_limit - 2.0

    # Stage 1: affine bi-Cayley graphs, largest feasible group order first.
    minN = best[0] // 2 + 1          # bi-Cayley order 2N must exceed the current best
    maxN = min(2000, moore // 2)
    if D >= 2 and d <= minN and minN <= maxN:
        budget1 = 0.55 * (deadline - time.monotonic())
        if budget1 > 1.0:
            try:
                n1, e1 = _affine_bicayley(d, D, seed, budget1, minN, maxN)
                if n1 > best[0] and lib.is_valid(n1, e1, d, D):
                    best = (n1, e1)
            except Exception:
                pass

    # Stage 2: voltage-lift search and grow-by-two from the best graph so far.
    budget2 = deadline - time.monotonic() - 0.5
    if budget2 > 1.0 and best[0] < moore:
        try:
            text = lib.run_c(OLD_C_SOURCE, [d, D, seed, budget2],
                             stdin_graph=best, timeout=budget2 + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass
    return best
