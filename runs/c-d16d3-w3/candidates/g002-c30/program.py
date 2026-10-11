"""Combined diameter-3 search: algebraic starts, then a dominating-set insertion engine,
then a squeeze engine (voltage lifts and annealed swaps) on the result.

Starts (all validated with lib.is_valid): conic blow-up of PG(2,q), arc-extended PG(2,q)
incidence graphs with greedy or conic A/B sets, W(q) for D >= 4, and K_{d,d} as fallback.

Engines (each result is validated, and a failed run keeps the previous graph):
  1. INSERT engine: adds a vertex on one side, joined to a greedy cover of the other side's
     radius-(D-1) balls, so ecc(new) <= D and old distances only shrink. Ruin-and-recreate
     perturbation with restoration of the best snapshot.
  2. SQUEEZE engine: voltage lifts over semidirect products Z_m x| Z_k, then grow-by-two
     with annealed degree-preserving edge swaps.
"""
import itertools
import random
import time

import lib


C_INSERT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define INF 100
typedef uint64_t u64;

static int D_, DEG_, CAP, W, n;
static int *deg, *adj, *col, *queue_, *cand, *dv, *sel, *best_sel;
static unsigned char *dist, *used;
static u64 *ball, *unc;
static unsigned long long rs = 88172645463325252ULL;

typedef struct { int n; int *deg; int *adj; int *col; } Snap;

static unsigned long long rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (unsigned long long)k); }
static double now(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int pc64(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void add_edge(int a, int b) {
    adj[(size_t)a * DEG_ + deg[a]++] = b;
    adj[(size_t)b * DEG_ + deg[b]++] = a;
}

static void recompute_dist(void) {
    for (int s = 0; s < n; s++) {
        unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++) row[x] = INF;
        row[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (row[v] == INF) {
                    row[v] = (unsigned char)(row[u] + 1);
                    queue_[t++] = v;
                }
            }
        }
    }
}

static int diam_ok(void) {
    for (int s = 0; s < n; s++) {
        const unsigned char *row = dist + (size_t)s * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] > D_) return 0;
    }
    return 1;
}

static void build_balls(void) {
    for (int v = 0; v < n; v++) {
        u64 *b = ball + (size_t)v * W;
        memset(b, 0, sizeof(u64) * (size_t)W);
        const unsigned char *row = dist + (size_t)v * CAP;
        for (int x = 0; x < n; x++)
            if (row[x] <= D_ - 1) b[x >> 6] |= 1ULL << (x & 63);
    }
}

/* Greedy set cover of all current vertices by balls of spare vertices of colour c.
   Returns the number of chosen neighbours (<= DEG_) written to best_sel, or -1. */
static int try_insert(int c, int restarts) {
    int nc = 0;
    for (int v = 0; v < n; v++)
        if (col[v] == c && deg[v] < DEG_) cand[nc++] = v;
    if (nc == 0) return -1;
    for (int r = 0; r < restarts; r++) {
        for (int w = 0; w < W; w++) unc[w] = 0;
        for (int x = 0; x < n; x++) unc[x >> 6] |= 1ULL << (x & 63);
        int uncount = n, ns = 0;
        memset(used, 0, (size_t)nc);
        while (uncount > 0 && ns < DEG_) {
            int bi = -1;
            long long bkey = -1;
            for (int i = 0; i < nc; i++) {
                if (used[i]) continue;
                const u64 *b = ball + (size_t)cand[i] * W;
                int g = 0;
                for (int w = 0; w < W; w++) g += pc64(b[w] & unc[w]);
                if (g == 0) continue;
                long long key = (long long)g * 4096 + (long long)(rnd() % 4096);
                if (key > bkey) { bkey = key; bi = i; }
            }
            if (bi < 0) break;
            used[bi] = 1;
            sel[ns++] = cand[bi];
            const u64 *b = ball + (size_t)cand[bi] * W;
            uncount = 0;
            for (int w = 0; w < W; w++) {
                unc[w] &= ~b[w];
                uncount += pc64(unc[w]);
            }
        }
        if (uncount == 0) {
            for (int k = 0; k < ns; k++) best_sel[k] = sel[k];
            return ns;
        }
    }
    return -1;
}

/* Insert a new vertex of colour 1-c adjacent to best_sel[0..ns-1]; update distances. */
static void insert_vertex(int c, int ns) {
    int v = n++;
    col[v] = 1 - c;
    deg[v] = 0;
    for (int k = 0; k < ns; k++) add_edge(v, best_sel[k]);
    for (int x = 0; x < v; x++) {
        int m = INF;
        for (int k = 0; k < ns; k++) {
            int t = dist[(size_t)x * CAP + best_sel[k]];
            if (t < m) m = t;
        }
        int dd = m + 1;
        if (dd > INF) dd = INF;
        dv[x] = dd;
    }
    for (int x = 0; x < v; x++) {
        dist[(size_t)x * CAP + v] = (unsigned char)dv[x];
        dist[(size_t)v * CAP + x] = (unsigned char)dv[x];
    }
    dist[(size_t)v * CAP + v] = 0;
    for (int x = 0; x < v; x++) {
        unsigned char *row = dist + (size_t)x * CAP;
        for (int y = 0; y < v; y++) {
            int t = dv[x] + dv[y];
            if (t > INF) t = INF;
            if (t < row[y]) row[y] = (unsigned char)t;
        }
    }
}

static void del_nbr(int u, int x) {
    int *a = adj + (size_t)u * DEG_;
    for (int j = 0; j < deg[u]; j++) {
        if (a[j] == x) {
            a[j] = a[deg[u] - 1];
            deg[u]--;
            return;
        }
    }
}

static void remove_vertex(int r) {
    int last = n - 1;
    for (int k = 0; k < deg[r]; k++) del_nbr(adj[(size_t)r * DEG_ + k], r);
    deg[r] = 0;
    if (r != last) {
        for (int k = 0; k < deg[last]; k++) {
            int u = adj[(size_t)last * DEG_ + k];
            int *a = adj + (size_t)u * DEG_;
            for (int j = 0; j < deg[u]; j++) {
                if (a[j] == last) { a[j] = r; break; }
            }
        }
        memcpy(adj + (size_t)r * DEG_, adj + (size_t)last * DEG_, sizeof(int) * (size_t)DEG_);
        deg[r] = deg[last];
        col[r] = col[last];
    }
    deg[last] = 0;
    col[last] = -1;
    n--;
    recompute_dist();
}

static void snap_init(Snap *s) {
    s->n = 0;
    s->deg = calloc((size_t)CAP, sizeof(int));
    s->adj = calloc((size_t)CAP * DEG_, sizeof(int));
    s->col = calloc((size_t)CAP, sizeof(int));
}

static void snap_save(Snap *s) {
    s->n = n;
    memcpy(s->deg, deg, sizeof(int) * (size_t)n);
    memcpy(s->col, col, sizeof(int) * (size_t)n);
    memcpy(s->adj, adj, sizeof(int) * (size_t)n * DEG_);
}

static void snap_load(Snap *s) {
    n = s->n;
    memcpy(deg, s->deg, sizeof(int) * (size_t)n);
    memcpy(col, s->col, sizeof(int) * (size_t)n);
    memcpy(adj, s->adj, sizeof(int) * (size_t)n * DEG_);
    recompute_dist();
}

static void emit_state(int nn, const int *dg, const int *ad) {
    long m = 0;
    for (int v = 0; v < nn; v++) m += dg[v];
    m /= 2;
    printf("%d %ld\n", nn, m);
    for (int v = 0; v < nn; v++)
        for (int k = 0; k < dg[v]; k++) {
            int u = ad[(size_t)v * DEG_ + k];
            if (v < u) printf("%d %d\n", v, u);
        }
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    int d = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (unsigned long long)atoll(argv[3]) * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();
    double tl = atof(argv[4]);
    DEG_ = d;

    int nin = 0, min_ = 0;
    if (scanf("%d %d", &nin, &min_) != 2) { nin = 0; min_ = 0; }
    if (nin < 0) nin = 0;
    if (min_ < 0) min_ = 0;
    int *eu = malloc(sizeof(int) * (size_t)(min_ + 2));
    int *ev = malloc(sizeof(int) * (size_t)(min_ + 2));
    int m_read = 0;
    for (int i = 0; i < min_; i++) {
        int a, b;
        if (scanf("%d %d", &a, &b) != 2) break;
        if (a < 0 || b < 0 || a >= nin || b >= nin || a == b) continue;
        eu[m_read] = a;
        ev[m_read] = b;
        m_read++;
    }
    if (nin == 0) {
        nin = 2;
        m_read = 1;
        eu[0] = 0;
        ev[0] = 1;
    }

    CAP = nin + 1500;
    W = (CAP + 63) / 64;
    deg = calloc((size_t)CAP, sizeof(int));
    adj = calloc((size_t)CAP * DEG_, sizeof(int));
    col = malloc(sizeof(int) * (size_t)CAP);
    queue_ = malloc(sizeof(int) * (size_t)CAP);
    cand = malloc(sizeof(int) * (size_t)CAP);
    dv = malloc(sizeof(int) * (size_t)CAP);
    sel = malloc(sizeof(int) * (size_t)DEG_ + sizeof(int));
    best_sel = malloc(sizeof(int) * (size_t)DEG_ + sizeof(int));
    dist = malloc((size_t)CAP * CAP);
    used = malloc((size_t)CAP);
    ball = calloc((size_t)CAP * W, sizeof(u64));
    unc = calloc((size_t)W, sizeof(u64));

    n = nin;
    for (int i = 0; i < n; i++) col[i] = -1;
    for (int i = 0; i < m_read; i++)
        if (deg[eu[i]] < DEG_ && deg[ev[i]] < DEG_) add_edge(eu[i], ev[i]);

    int bip = 1;
    for (int s = 0; s < n; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int h = 0, t = 0;
        queue_[t++] = s;
        while (h < t) {
            int u = queue_[h++];
            for (int k = 0; k < deg[u]; k++) {
                int v = adj[(size_t)u * DEG_ + k];
                if (col[v] < 0) { col[v] = 1 - col[u]; queue_[t++] = v; }
                else if (col[v] == col[u]) bip = 0;
            }
        }
    }
    recompute_dist();
    if (!bip || !diam_ok()) {
        emit_state(n, deg, adj);
        return 0;
    }

    Snap best, tmp;
    snap_init(&best);
    snap_init(&tmp);
    snap_save(&best);
    int best_n = n;

    double t0 = now();
    while (now() - t0 < tl) {
        if (n + 2 >= CAP) break;
        build_balls();
        int inserted = 0;
        int first = rndint(2);
        for (int t = 0; t < 2 && !inserted; t++) {
            int c = (t == 0) ? first : 1 - first;
            int ns = try_insert(c, 6);
            if (ns > 0) {
                insert_vertex(c, ns);
                inserted = 1;
            }
        }
        if (inserted) {
            if (n > best_n) {
                best_n = n;
                snap_save(&best);
            }
            continue;
        }
        snap_save(&tmp);
        int k = 1 + rndint(2);
        for (int j = 0; j < k && n > 2; j++) remove_vertex(rndint(n));
        if (!diam_ok()) snap_load(&tmp);
        if (n < best_n - 3) snap_load(&best);
    }

    emit_state(best.n, best.deg, best.adj);
    return 0;
}
"""


C_SQUEEZE = r'''
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

static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
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
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    return 1;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(10);
        int p = r < 4 ? 1 : r < 7 ? 2 : r < 9 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int N = (int)((target + 2 * p - 1) / (2 * p)) + rndint(2);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || 2L * p * N > moore || 2 * p * N > MAXN) {
            if (++fails > 1000) return;
            continue;
        }
        if (!random_group(N, &G)) continue;
        int steps = 200 + 400000 / (2 * p * N);
        if (lift_try(&cand, p, N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

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
        double lift_share = had_start ? 0.05 : 0.6;
        lift_search(&best, t0 + (t_end - t0) * lift_share);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Structured starts.
# ----------------------------------------------------------------------------

def known_start(d, D):
    """Moore graph or Araujo-Pardo/Lopez for D = 3."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def conic_blowup(d, D):
    """Twin blow-up of PG(2,q), q = d-3 odd, duplicating conic points and dual-conic lines."""
    q = d - 3
    if D != 3 or q < 3 or q % 2 == 0 or not lib.is_prime_power(q):
        return None
    F = lib.GF(q)
    pts = lib.projective_points(q)
    index = {v: i for i, v in enumerate(pts)}
    m = len(pts)
    conic = [(1, t, F.mul(t, t)) for t in range(q)] + [(0, 0, 1)]
    if any(v not in index for v in conic):
        return None
    arc = [index[v] for v in conic]
    n0, base = lib.projective_plane_incidence(q)
    pcopy = {i: [i] for i in range(m)}
    lcopy = {j: [m + j] for j in range(m)}
    n = n0
    for i in arc:
        pcopy[i].append(n)
        n += 1
    for j in arc:
        lcopy[j].append(n)
        n += 1
    edges = set()
    for u, v in base:
        i, j = u, v - m
        for a in pcopy[i]:
            for b in lcopy[j]:
                edges.add((a, b) if a < b else (b, a))
    return n, sorted(edges)


def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, nbr):
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, pl, lp, index, _pts = _pg_data(q)
        SA = _greedy_side(m, s, pl, rng, 40, deadline)
        SB = _greedy_side(m, s, lp, rng, 40, deadline)
        if s >= 2 and q >= 3:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, pl):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, lp):
                SB = cs
        if not (_loads_ok(SA, s, m, pl) and _loads_ok(SB, s, m, lp)):
            continue
        out.append(_arc_graph(m, edges, pl, lp, SA, SB))
    return out


def _gq_w(q):
    """Incidence graph of W(q), the generalized quadrangle (diameter 4)."""
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
    edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
    return 2 * P, edges


def starts(d, D, deadline, rng):
    out = []
    ks = known_start(d, D)
    if ks is not None:
        out.append(ks)
    cb = conic_blowup(d, D)
    if cb is not None:
        out.append(cb)
    if D >= 3:
        out.extend(_arc_extensions(d, deadline, rng))
    if D >= 4 and d - 1 <= 6:
        for q in range(min(d - 1, 5), 1, -1):
            if lib.is_prime_power(q):
                out.append(_gq_w(q))
                break
    return out


# ----------------------------------------------------------------------------
# C engine drivers.
# ----------------------------------------------------------------------------

def _run(source, args, graph, budget, elapsed_left):
    """Run a C engine; return a validated (n, edges) or None."""
    timeout = max(1.0, min(budget + 3.0, elapsed_left))
    try:
        text = lib.run_c(source, args, stdin_graph=graph, timeout=timeout)
        return lib.parse_graph_text(text)
    except (RuntimeError, ValueError):
        return None


def build(d, D, seed, time_limit):
    """Return the best valid (n, edges) found within about 85% of time_limit."""
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    def left():
        return time_limit - (time.monotonic() - t0)

    rng = random.Random(seed * 7919 + d)
    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2

    for g in starts(d, D, t0 + 0.15 * time_limit, rng):
        try:
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = g
        except Exception:
            pass

    hard_end = 0.85 * time_limit - 1.0

    # Phase A: dominating-set insertion engine.
    rem = hard_end - (time.monotonic() - t0)
    if rem > 1.5:
        budget = max(0.5, 0.6 * rem)
        r = _run(C_INSERT, [d, D, seed * 31 + 1, f"{budget:.2f}"],
                 best, budget, left() - 0.5)
        if r is not None and r[0] > best[0] and lib.is_valid(r[0], r[1], d, D):
            best = r

    # Phase B: squeeze engine (voltage lifts, then grow-by-two with annealed swaps).
    rem = hard_end - (time.monotonic() - t0)
    if rem > 1.5:
        budget = max(0.5, rem - 0.5)
        r = _run(C_SQUEEZE, [d, D, seed * 31 + 2, f"{budget:.2f}"],
                 best, budget, left() - 0.5)
        if r is not None and r[0] > best[0] and lib.is_valid(r[0], r[1], d, D):
            best = r

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
