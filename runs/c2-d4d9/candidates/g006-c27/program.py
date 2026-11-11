"""Combined bi-Cayley / voltage-lift search for bipartite degree-diameter graphs.

The C engine works on one group table (metacyclic Z_m x| Z_k or PSL/SL(2,q) for prime q)
and lifts it over a base multigraph with p <= 4 vertices per side. Vertex (i, x) is joined to
(p+j, x*g) for each dart (i, j, g). Left multiplication is an automorphism acting regularly on
each fibre, so the diameter check needs only 2p BFS runs from fibre representatives.
Voltages are annealed with sawtooth reheating to minimise unreached pairs. Successes raise the
bar, giving an ascending ladder of orders. The last quarter of the time goes to growing the best
graph by two vertices per side with repair annealing.

Python supplies algebraic starts, keeps the largest graph that lib.is_valid accepts, and falls
back to K_{d,d} or the known start.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 10240
#define MAXD 16
#define MAXW (MAXV / 64)
#define MAXG 3200
#define MAXP 4

#define T_HI 3.0
#define T_LO 0.05
#define CYCLES 3.0

static int d, D;

/* ------------------------------------------------------------ utilities */

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return (double)ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod_l(long b, long e, long m) {
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

static long cap_order(void) {
    long mb = moore_bound();
    return mb < MAXV ? mb : MAXV;
}

/* ------------------------------------------------------------ group tables */

static int NG = 0, EID = 0;
static uint16_t TB[MAXG * MAXG];   /* TB[x*NG+y] = x*y */

/* Z_m x|_r Z_k, element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
static void build_meta(int m, int k, int r) {
    NG = m * k;
    static int pw[MAXG];
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long)pw[b - 1] * r % m);
    for (int x = 0; x < NG; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < NG; y++) {
            int c = y / k, e = y % k;
            int aa = (a + pw[b] * c) % m;
            int bb = (b + e) % k;
            TB[(size_t)x * NG + y] = (uint16_t)(aa * k + bb);
        }
    }
    EID = 0;
}

/* PSL(2,q) (psl = 1) or SL(2,q) for prime q. */
static int MQ, MPSL;
static int *IDX = NULL;
static int IDXCAP = 0;
static int MATE[MAXG][4];

static int canon_key(int a, int b, int c, int e) {
    int q = MQ;
    int k = ((a * q + b) * q + c) * q + e;
    if (!MPSL) return k;
    int na = (q - a) % q, nb = (q - b) % q, nc = (q - c) % q, ne = (q - e) % q;
    int kn = ((na * q + nb) * q + nc) * q + ne;
    return k < kn ? k : kn;
}

static int build_matrix(int q, int psl) {
    MQ = q;
    MPSL = psl;
    int ks = q * q * q * q;
    if (ks > IDXCAP) {
        free(IDX);
        IDX = malloc(sizeof(int) * (size_t)ks);
        IDXCAP = ks;
    }
    for (int i = 0; i < ks; i++) IDX[i] = -1;
    int cnt = 0;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            for (int c = 0; c < q; c++)
                for (int e = 0; e < q; e++) {
                    if ((((a * e - b * c) % q) + q) % q != 1) continue;
                    int own = ((a * q + b) * q + c) * q + e;
                    if (canon_key(a, b, c, e) != own) continue;
                    if (cnt >= MAXG) { NG = 0; return 0; }
                    MATE[cnt][0] = a;
                    MATE[cnt][1] = b;
                    MATE[cnt][2] = c;
                    MATE[cnt][3] = e;
                    IDX[own] = cnt;
                    cnt++;
                }
    NG = cnt;
    int bad = 0;
    for (int x = 0; x < NG && !bad; x++) {
        int a = MATE[x][0], b = MATE[x][1], c = MATE[x][2], e = MATE[x][3];
        for (int y = 0; y < NG; y++) {
            int a2 = MATE[y][0], b2 = MATE[y][1], c2 = MATE[y][2], e2 = MATE[y][3];
            int pa = (a * a2 + b * c2) % q;
            int pb = (a * b2 + b * e2) % q;
            int pc = (c * a2 + e * c2) % q;
            int pe = (c * b2 + e * e2) % q;
            int v = IDX[canon_key(pa, pb, pc, pe)];
            if (v < 0) { bad = 1; break; }
            TB[(size_t)x * NG + y] = (uint16_t)v;
        }
    }
    if (bad) { NG = 0; return 0; }
    EID = IDX[canon_key(1, 0, 0, 1)];
    return 1;
}

/* ------------------------------------------------------------ candidate groups */

typedef struct { int type, q, psl, m, k, r, N; } Cand;   /* type 0 meta, 1 matrix */
static Cand MATC[16];
static int nmat = 0;

static void init_matrix_list(void) {
    static const int qs[] = {5, 7, 11, 13, 17};
    nmat = 0;
    for (int i = 0; i < 5; i++)
        for (int psl = 0; psl < 2; psl++) {
            int q = qs[i];
            int N = q * (q * q - 1);
            if (psl) N /= 2;
            if (N > MAXG || N < 2 * d) continue;
            Cand c = {1, q, psl, 0, 0, 0, N};
            MATC[nmat++] = c;
        }
}

static int apply_group(const Cand *c) {
    if (c->type == 0) build_meta(c->m, c->k, c->r);
    else build_matrix(c->q, c->psl);
    return NG == c->N;
}

/* Uniformly random metacyclic group of order N (reservoir over (m, k, r)). */
static int random_meta(int N, Cand *out) {
    long count = 0;
    int bm = 0, bk = 0, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod_l(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)count) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (!count) return 0;
    Cand c = {0, 0, 0, bm, bk, br, N};
    *out = c;
    return 1;
}

/* ------------------------------------------------------------ graphs */

typedef struct {
    int n;
    int deg[MAXV];
    int adj[MAXV][MAXD];
    unsigned char side[MAXV];
} Graph;

static Graph BEST, CAND, WORK;
static uint64_t RA[MAXV * MAXW], RB[MAXV * MAXW];
static int badv[MAXV];

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

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
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
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

static int graph_ok(const Graph *g) {
    if (g->n <= 0 || g->n > MAXV) return 0;
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

static int stamp_arr[MAXV];
static int tick = 0;
static int qbuf[MAXV];

/* Number of vertices within distance D of src (src included). */
static int ball(const Graph *g, int src) {
    if (++tick == 0x7fffffff) {
        memset(stamp_arr, 0, sizeof stamp_arr);
        tick = 1;
    }
    int head = 0, tail = 0;
    stamp_arr[src] = tick;
    qbuf[tail++] = src;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = qbuf[head];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (stamp_arr[u] != tick) {
                    stamp_arr[u] = tick;
                    qbuf[tail++] = u;
                }
            }
        }
    }
    return tail;
}

static void read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXV || m < 0) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    static int queue[MAXV];
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = 1 - g->side[v];
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
            }
        }
    }
    if (!graph_ok(g)) g->n = 0;
}

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
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

/* ------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;
static Dart DT[MAXD * MAXP], DTB[MAXD * MAXP];

/* Random d-regular bipartite base multigraph with p vertices per side, connected. */
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

/* A voltage not used by other darts on the same base pair (skip excluded). */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j) {
    for (;;) {
        int g = rndint(NG), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int make_darts(int p, Dart *dt) {
    int M[MAXP][MAXP];
    make_base(p, M);
    int nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = (c == 0) ? EID : fresh_voltage(dt, nd, -1, i, j);
                nd++;
            }
    return nd;
}

/* Vertex (f, x) = f*NG + x. Left fibres 0..p-1, right fibres p..2p-1. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    g->n = 2 * p * NG;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * NG);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < NG; x++) {
            int a = dt[t].i * NG + x;
            int b = (p + dt[t].j) * NG + TB[(size_t)x * NG + dt[t].g];
            add_edge(g, a, b);
        }
}

/* Sum over fibre representatives of unreached vertices (0 = diameter <= D). */
static long sym_bad(const Graph *g, int p) {
    long bad = 0;
    for (int f = 0; f < 2 * p; f++) bad += g->n - ball(g, f * NG + EID);
    return bad;
}

/* Anneal voltages on a random base. On success CAND holds the valid lift. */
static int lift_sa(int p, double until) {
    int nd = make_darts(p, DT);
    build_lift(&CAND, p, DT, nd);
    long cur = sym_bad(&CAND, p);
    if (cur == 0) return 1;
    double start = now(), span = until - start;
    if (span <= 0.0) return 0;
    long bestc = cur;
    memcpy(DTB, DT, sizeof(Dart) * (size_t)nd);
    double temp = T_HI;
    long it = 0;
    while (cur > 0) {
        if ((++it & 7) == 0) {
            double t = now();
            if (t >= until) break;
            double ph = (t - start) / span * CYCLES;
            ph -= floor(ph);
            temp = T_HI * pow(T_LO / T_HI, ph);
        }
        int tt = rndint(nd);
        int old = DT[tt].g;
        DT[tt].g = fresh_voltage(DT, nd, tt, DT[tt].i, DT[tt].j);
        build_lift(&CAND, p, DT, nd);
        long nc = sym_bad(&CAND, p);
        long df = nc - cur;
        if (df <= 0 || rnd01() < exp(-(double)df / temp)) {
            cur = nc;
            if (cur < bestc) {
                bestc = cur;
                memcpy(DTB, DT, sizeof(Dart) * (size_t)nd);
            }
        } else {
            DT[tt].g = old;
        }
    }
    if (bestc > 0) return 0;
    build_lift(&CAND, p, DTB, nd);
    return 1;
}

/* One ladder step: pick a group and p with 2pN above the current best, then anneal. */
static int attempt(double until) {
    long cap = cap_order();
    long lo = (long)BEST.n + 2;
    if (lo > cap) return 0;
    int p = 1 + rndint(MAXP);
    Cand c;
    int have = 0;
    if (rnd01() < 0.4) {
        int fe[16], nf = 0;
        for (int i = 0; i < nmat; i++) {
            long n2 = 2L * p * MATC[i].N;
            if (n2 >= lo && n2 <= cap) fe[nf++] = i;
        }
        if (nf > 0) { c = MATC[fe[rndint(nf)]]; have = 1; }
    }
    if (!have) {
        long span = BEST.n / 40;
        if (span < 2) span = 2;
        long target = lo + rndint((int)span);
        long N = (target + 2L * p - 1) / (2L * p) + rndint(2);
        if (2L * p * N > cap) N = cap / (2L * p);
        if (N > MAXG) N = MAXG;
        if (N < 2 * d || 2L * p * N < lo) return 0;
        if (!random_meta((int)N, &c)) return 0;
    }
    if (!apply_group(&c)) return 0;
    long n2 = 2L * p * NG;
    if (n2 < lo || n2 > cap) return 0;
    double rem = until - now();
    if (rem < 0.05) return 0;
    double slice = 2.0 + 4.0 * (double)n2 / 6000.0;
    if (slice > rem) slice = rem;
    if (!lift_sa(p, now() + slice)) return 0;
    if (CAND.n > BEST.n && graph_ok(&CAND)) {
        copy_graph(&BEST, &CAND);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ grow by two */

static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > cap_order()) return 0;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    static int used[MAXV];
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
    return graph_ok(work);
}

static void grow_search(double until) {
    while (now() < until && (long)BEST.n + 2 <= cap_order()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&BEST, &WORK, now() + slice)) copy_graph(&BEST, &WORK);
    }
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
    double usable = limit - 1.0;
    if (usable < limit * 0.5) usable = limit * 0.5;
    double t_end = t0 + usable;

    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    read_start(&BEST);
    if (BEST.n == 0) complete_bipartite(&BEST);
    init_matrix_list();

    if ((long)BEST.n < moore_bound()) {
        double t_ladder = t0 + usable * 0.75;
        while (now() < t_ladder && (long)BEST.n + 2 <= cap_order())
            attempt(t_ladder);
        if (now() < t_end && (long)BEST.n + 2 <= cap_order())
            grow_search(t_end);
    }
    if (!graph_ok(&BEST)) complete_bipartite(&BEST);
    print_graph(&BEST);
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


def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def known_starts(d, D):
    """Algebraic candidate graphs (filtered by lib.is_valid by the caller)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(_try(lib.projective_plane_incidence, d - 1))
    if D >= 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(_try(lib.araujo_lopez_graph, d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_try(_gq_w, q))
    return [c for c in out if c is not None]


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

    if d > 16 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
