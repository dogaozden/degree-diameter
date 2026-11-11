"""Combined search: voltage lifts over semidirect and matrix groups, annealed on the
fibre-transitive diameter check, followed by grow-by-two annealing.

Merged from two parents:
  * Lifts over a group G act on each fibre by left multiplication, so the diameter is <= D
    iff each of the 2p fibre representatives reaches all n vertices within D steps (2p BFS
    runs). This is the cheap check from the first parent.
  * Groups come from two families: semidirect products Z_m x| Z_k (uniform over valid (m,k,r))
    and matrix groups PSL/PGL(2,q), SL(2,8), PSL(2,16) (from the second parent).
  * Voltage search is simulated annealing (second parent's acceptance rule), not greedy.
  * Algebraic starts from Python (PG(2,q), W(q), Araujo-Pardo-Lopez, K_{d,d}) seed the C engine.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define MATMAX 4200
#define CODEMAX 130400

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

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

/* ------------------------------------------------------------ distance checks */

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

static int bfs_stamp[MAXN];
static int bfs_tick = 0;
static int bfs_q[MAXN];

/* Number of vertices within distance D of s (s included). */
static int ball_size(const Graph *g, int s) {
    if (++bfs_tick == 0x7fffffff) {
        memset(bfs_stamp, 0, sizeof bfs_stamp);
        bfs_tick = 1;
    }
    int head = 0, tail = 0;
    bfs_stamp[s] = bfs_tick;
    bfs_q[tail++] = s;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        for (; head < end; head++) {
            int v = bfs_q[head];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (bfs_stamp[u] != bfs_tick) {
                    bfs_stamp[u] = bfs_tick;
                    bfs_q[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Lift with fibre size N and 2p fibres (fibre u = vertices u*N .. u*N+N-1). The group
 * acts regularly on each fibre by automorphisms, so one vertex per fibre suffices.
 * Returns the number of unreached (representative, vertex) pairs; 0 means valid. */
static long sym_bad(const Graph *g, int p, int N) {
    long bad = 0;
    for (int u = 0; u < 2 * p; u++) bad += g->n - ball_size(g, u * N);
    return bad;
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

/* ------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------ finite fields */

typedef struct {
    int add[32][32], mul[32][32], neg[32], inv[32];
} Field;
static Field F;
static int MQ, MMODE;
static int CODE2IDX[CODEMAX];
static int MAT[MATMAX][4];

static int gf2mul(int a, int b, int k, int poly) {
    int r = 0;
    for (int i = 0; i < k; i++)
        if ((b >> i) & 1) r ^= a << i;
    for (int i = 2 * k - 2; i >= k; i--)
        if ((r >> i) & 1) r ^= poly << (i - k);
    return r;
}

static void field_init(int q) {
    memset(&F, 0, sizeof F);
    if (q == 8 || q == 16) {
        int k = (q == 8) ? 3 : 4;
        int poly = (q == 8) ? 0xB : 0x13;
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                F.add[i][j] = i ^ j;
                F.mul[i][j] = gf2mul(i, j, k, poly);
            }
        for (int i = 0; i < q; i++) F.neg[i] = i;
    } else {
        for (int i = 0; i < q; i++)
            for (int j = 0; j < q; j++) {
                F.add[i][j] = (i + j) % q;
                F.mul[i][j] = (i * j) % q;
            }
        for (int i = 0; i < q; i++) F.neg[i] = (q - i) % q;
    }
    for (int i = 1; i < q; i++)
        for (int j = 1; j < q; j++)
            if (F.mul[i][j] == 1) F.inv[i] = j;
}

/* ------------------------------------------------------------ matrix groups */

static int enc(int a, int b, int c, int e) { return ((a * MQ + b) * MQ + c) * MQ + e; }

static int norm_code(int a, int b, int c, int e) {
    if (MMODE == 2) {
        int f = a ? a : (b ? b : (c ? c : e));
        int iv = F.inv[f];
        return enc(F.mul[a][iv], F.mul[b][iv], F.mul[c][iv], F.mul[e][iv]);
    }
    int c1 = enc(a, b, c, e);
    if (MMODE == 0) {
        int c2 = enc(F.neg[a], F.neg[b], F.neg[c], F.neg[e]);
        if (c2 < c1) c1 = c2;
    }
    return c1;
}

/* mode 0: PSL(2,q) (det 1, M ~ -M), mode 2: PGL(2,q) (det != 0, M ~ scalar * M). */
static int matrix_group_build(int q, int mode) {
    MQ = q;
    MMODE = mode;
    field_init(q);
    int Q4 = q * q * q * q;
    for (int i = 0; i < Q4; i++) CODE2IDX[i] = -1;
    int N = 0;
    for (int code = 0; code < Q4; code++) {
        int m3 = code % q;
        int m2 = (code / q) % q;
        int m1 = (code / (q * q)) % q;
        int m0 = code / (q * q * q);
        int det = F.add[F.mul[m0][m3]][F.neg[F.mul[m1][m2]]];
        if (mode == 2) {
            if (det == 0) continue;
        } else if (det != 1) {
            continue;
        }
        if (norm_code(m0, m1, m2, m3) != code) continue;
        if (N >= MATMAX) return 0;
        CODE2IDX[code] = N;
        MAT[N][0] = m0;
        MAT[N][1] = m1;
        MAT[N][2] = m2;
        MAT[N][3] = m3;
        N++;
    }
    return N;
}

static int mat_mul(int x, int y) {
    const int *X = MAT[x], *Y = MAT[y];
    int a = F.add[F.mul[X[0]][Y[0]]][F.mul[X[1]][Y[2]]];
    int b = F.add[F.mul[X[0]][Y[1]]][F.mul[X[1]][Y[3]]];
    int c = F.add[F.mul[X[2]][Y[0]]][F.mul[X[3]][Y[2]]];
    int e = F.add[F.mul[X[2]][Y[1]]][F.mul[X[3]][Y[3]]];
    return CODE2IDX[norm_code(a, b, c, e)];
}

/* ------------------------------------------------------------ current group */

typedef struct {
    int kind;      /* 0 = semidirect Z_m x| Z_k, 1 = matrix group (tables above) */
    int N;
    int m, k, r;
    int rp[MAXN];  /* semidirect: rp[b] = r^b mod m */
} Grp;
static Grp GR;

/* Element (a,b) = a*k+b, (a,b)(c,e) = (a + r^b c, b + e). Identity is index 0. */
static int gmul(int x, int y) {
    if (GR.kind == 1) return mat_mul(x, y);
    int k = GR.k;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    int a2 = (int)(((long)a + (long)GR.rp[b] * c) % GR.m);
    return a2 * k + (b + e) % k;
}

/* Uniform over the valid (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
static int random_semidirect(int N) {
    long count = 0;
    int bm = 1, bk = N, br = 1;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            count++;
            if (rndint((int)(count < 2000000000L ? count : 2000000000L)) == 0) {
                bm = m; bk = k; br = r;
            }
        }
    }
    if (!count) return 0;
    GR.kind = 0;
    GR.N = N;
    GR.m = bm;
    GR.k = bk;
    GR.r = br;
    GR.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) GR.rp[b] = (int)((long)GR.rp[b - 1] * br % bm);
    return 1;
}

/* ------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p+p vertices, connected. */
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

static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

/* A voltage not used by another dart between the same pair of base vertices. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Simulated annealing over the voltages of a random base graph. On success out holds
 * the valid lift with 2pN vertices. */
static int lift_sa(Graph *out, int p, int N, int steps) {
    static Graph wg;
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
    build_lift(&wg, p, N, dt, nd);
    long bad = sym_bad(&wg, p, N);
    double T0 = 0.3 + 2.0 * rnd01();
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > t_end) return 0;
        double T = T0 * (1.0 - (double)s / steps) + 0.05;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(&wg, p, N, dt, nd);
        long nb = sym_bad(&wg, p, N);
        long df = nb - bad;
        if (df <= 0 || rnd01() < exp(-(double)df / T)) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    build_lift(out, p, N, dt, nd);   /* dt now holds the accepted state */
    return 1;
}

/* Matrix group candidates: order, field, mode. */
static const int MQS[12] = {5, 5, 7, 7, 8, 11, 11, 13, 13, 16, 17, 19};
static const int MMODE_T[12] = {0, 2, 0, 2, 0, 0, 2, 0, 2, 0, 0, 0};
static const int MORD[12] = {60, 120, 168, 336, 504, 660, 1320, 1092, 2184, 4080, 2448, 3420};

static void lift_search(Graph *best, double until) {
    static Graph out;
    long moore = moore_bound();
    long cap = moore < MAXN ? moore : MAXN;
    while (now() < until) {
        if (best->n + 2 > cap) return;
        int r = rndint(10);
        int p = r < 3 ? 1 : r < 6 ? 2 : r < 8 ? 3 : 4;
        long lo = best->n / (2 * p) + 1;
        long span = best->n / 40;
        if (span < 3) span = 3;
        long Nmax = cap / (2 * p);
        long N = best->n == 0 ? d + rndint(4) : lo + rndint((int)span);
        if (N > Nmax) N = Nmax;
        if (N < d) continue;
        if (2L * p * N <= best->n) continue;

        int ok = 0;
        if (rndint(100) < 35) {
            int cand[12], nc = 0;
            for (int c = 0; c < 12; c++)
                if (MORD[c] >= lo && MORD[c] <= N + span && MORD[c] <= Nmax)
                    cand[nc++] = c;
            if (nc > 0) {
                int c = cand[rndint(nc)];
                int n2 = matrix_group_build(MQS[c], MMODE_T[c]);
                if (n2 > 0) {
                    GR.kind = 1;
                    GR.N = n2;
                    ok = 1;
                }
            }
        }
        if (!ok) {
            if (!random_semidirect((int)N)) continue;
        }
        N = GR.N;
        if (N < d) continue;
        long n2 = 2L * p * N;
        if (n2 <= best->n || n2 > cap) continue;
        long steps = 3000 + 6000000L / n2;
        if (lift_sa(&out, p, (int)N, (int)steps) && out.n > best->n && is_valid(&out))
            copy_graph(best, &out);
    }
}

/* ------------------------------------------------------------ grow by two */

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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double lift_end = t0 + (t_end - t0) * (best.n > 0 ? 0.8 : 0.85);
        lift_search(&best, lift_end);
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (validity is re-checked by the caller)."""
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

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    for n, e in known_starts(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
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
