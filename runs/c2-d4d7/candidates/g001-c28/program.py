"""Group-table bi-Cayley and voltage-lift search for bipartite degree-diameter graphs.

New construction: instead of only cyclic-by-cyclic semidirect groups, the C engine now
builds lifts over general finite groups given by multiplication tables. The groups are
semidirect products Z_m x| Z_k, PSL(2,p) and PGL(2,p) for small primes p (times cyclic
factors), and their products. A base multigraph on p+p vertices (p = 1 or 2) is lifted
over the group, with edges (A, i, x) ~ (B, j, x*g). The left regular action makes the
diameter check cheap: BFS from one representative per fibre suffices. Voltages are
hill-climbed. Any lift that beats the current graph is kept. The parent's grow-by-two
annealing finishes the budget. The Python side keeps the algebraic starts and a K_{d,d}
fallback, and every result is checked with lib.is_valid.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-table version.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Lifts of a random d-regular base multigraph on p+p vertices (p = 1, 2) over a group G
 *    given by a multiplication table. G is one of: Z_m x|_r Z_k, PSL(2,p) x Z_c,
 *    PGL(2,p) x Z_c. Voltages are hill-climbed with an orbit-reduced diameter test.
 * 2. Grow by two: insert one vertex per side and anneal degree-preserving swaps.
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
#define MAXG 1100
#define MAXB 1100
#define MAXC 400
#define PP 28561   /* 13^4, for normalised 2x2 matrices over GF(p), p <= 13 */

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

/* ------------------------------------------------------------------ groups as tables */

static int GN;
static int GT[MAXG * MAXG];   /* GT[x*GN + y] = x*y */
static int BT[MAXB * MAXB];   /* base table for PSL/PGL */
static int BN;
static int PIDX[PP];
static int PE[MAXB][4];

static int gmul(int x, int y) { return GT[x * GN + y]; }

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void build_sd(int m, int k, int r) {
    int rp[MAXG];
    rp[0] = 1 % m;
    for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    GN = m * k;
    for (int x = 0; x < GN; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < GN; y++) {
            int c = y / k, e = y % k;
            GT[x * GN + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
}

static int inv_mod(int a, int p) {
    for (int x = 1; x < p; x++)
        if (a * x % p == 1) return x;
    return 0;
}

static int is_square_mod(int a, int p) {
    for (int x = 1; x < p; x++)
        if (x * x % p == a) return 1;
    return 0;
}

/* BT = PGL(2,p) (pgl = 1) or PSL(2,p) (pgl = 0), as normalised projective classes. */
static int build_proj(int p, int pgl) {
    int P4 = p * p * p * p;
    int cnt = 0;
    for (int i = 0; i < P4; i++) PIDX[i] = -1;
    for (int a = 0; a < p; a++)
    for (int b = 0; b < p; b++)
    for (int c = 0; c < p; c++)
    for (int e = 0; e < p; e++) {
        int v[4] = {a, b, c, e};
        int first = -1;
        for (int t = 0; t < 4; t++) if (v[t]) { first = v[t]; break; }
        if (first != 1) continue;               /* normalised: first nonzero entry is 1 */
        int det = ((a * e - b * c) % p + p) % p;
        if (det == 0) continue;
        if (!pgl && !is_square_mod(det, p)) continue;  /* PSL: square determinant */
        if (cnt >= MAXB) return 0;
        PIDX[((a * p + b) * p + c) * p + e] = cnt;
        PE[cnt][0] = a; PE[cnt][1] = b; PE[cnt][2] = c; PE[cnt][3] = e;
        cnt++;
    }
    BN = cnt;
    for (int i = 0; i < cnt; i++)
    for (int j = 0; j < cnt; j++) {
        int *A = PE[i], *B = PE[j];
        int m[4];
        m[0] = (A[0] * B[0] + A[1] * B[2]) % p;
        m[1] = (A[0] * B[1] + A[1] * B[3]) % p;
        m[2] = (A[2] * B[0] + A[3] * B[2]) % p;
        m[3] = (A[2] * B[1] + A[3] * B[3]) % p;
        int f = 0;
        for (int t = 0; t < 4; t++) if (m[t]) { f = m[t]; break; }
        if (f == 0) return 0;
        int s = inv_mod(f, p);
        for (int t = 0; t < 4; t++) m[t] = m[t] * s % p;
        int id = PIDX[((m[0] * p + m[1]) * p + m[2]) * p + m[3]];
        if (id < 0) return 0;
        BT[i * BN + j] = id;
    }
    return 1;
}

/* GT = BT x Z_c. */
static void expand_cyclic(int c) {
    GN = BN * c;
    for (int x = 0; x < GN; x++) {
        int g1 = x / c, t = x % c;
        for (int y = 0; y < GN; y++) {
            int g2 = y / c, s = y % c;
            GT[x * GN + y] = BT[g1 * BN + g2] * c + (t + s) % c;
        }
    }
}

typedef struct { int type, a, b, c, N; } Cand;   /* type 1 PSL(2,a) x Z_b, type 2 PGL(2,a) x Z_b */
static Cand CL[MAXC];
static int ncand = 0;

static void build_candidates(void) {
    ncand = 0;
    int ps[5] = {3, 5, 7, 11, 13};
    for (int pi = 0; pi < 5; pi++)
    for (int pgl = 0; pgl < 2; pgl++) {
        int p = ps[pi];
        int bn = p * (p * p - 1) / (pgl ? 1 : 2);
        for (int c = 1; bn * c <= MAXG - 1; c++) {
            if (ncand >= MAXC) return;
            CL[ncand].type = pgl ? 2 : 1;
            CL[ncand].a = p;
            CL[ncand].b = c;
            CL[ncand].c = 0;
            CL[ncand].N = bn * c;
            ncand++;
        }
    }
}

/* Random metacyclic group of order N, chosen through a random divisor m. */
static int pick_sd(int N) {
    int divs[MAXG], nd = 0;
    for (int m = 1; m <= N; m++) if (N % m == 0) divs[nd++] = m;
    for (int t = 0; t < 50; t++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        int r = rndint(m);
        if (gcd(r, m) != 1) continue;
        if (powmod(r, k, m) != 1 % m) continue;
        build_sd(m, k, r);
        return 1;
    }
    return 0;
}

/* Set the current group to one with order in [lo, hi]. */
static int pick_group(int lo, int hi) {
    if (hi > MAXG - 1) hi = MAXG - 1;
    if (lo < 2) lo = 2;
    if (lo > hi) return 0;
    for (int t = 0; t < 200; t++) {
        if (ncand > 0 && rndint(2) == 0) {
            Cand *c = &CL[rndint(ncand)];
            if (c->N < lo || c->N > hi) continue;
            if (!build_proj(c->a, c->type == 2)) continue;
            expand_cyclic(c->b);
            return 1;
        }
        int N = lo + rndint(hi - lo + 1);
        if (pick_sd(N)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------------ lifts over GT */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Edge: (A,i,x) ~ (B,j,x*g). Left multiplication by any a is an automorphism. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective: BFS from the 2p fibre representatives (element 0).
 * Returns the number of (representative, vertex) pairs at distance > D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int nv = g->n, N = GN;
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

/* Hill-climb voltages of one random base multigraph over the current group. */
static int lift_try(Graph *g, int p, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j);
                nd++;
            }
    build_lift(g, p, dt, nd);
    long bad = orbit_bad(g, p);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j);
        build_lift(g, p, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, dt, nd);
    return bad == 0;
}

/* Search group lifts strictly larger than the current best. */
static void group_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int p = rndint(3) == 0 ? 2 : 1;
        long need = best->n + 2;
        long Nhi = moore / (2L * p);
        long Nlo = (need + 2L * p - 1) / (2L * p);
        if (Nlo > Nhi) {
            p = 1;
            Nhi = moore / 2;
            Nlo = (need + 1) / 2;
            if (Nlo > Nhi) return;
        }
        if (!pick_group((int)Nlo, (int)Nhi)) continue;
        for (int a = 0; a < 2 && now() < until; a++) {
            if (lift_try(&cand, p, 6000, until) && is_valid(&cand) && cand.n > best->n) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

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
    if (best.n == 0) complete_bipartite(&best);

    build_candidates();
    if (D >= 2 && best.n < moore_bound()) {
        group_search(&best, t0 + (t_end - t0) * 0.85);
        if (best.n > 0) grow_search(&best, t_end);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
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
