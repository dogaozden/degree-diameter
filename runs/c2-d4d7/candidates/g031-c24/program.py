"""Bold change for d=4 D=7: explicit non-metacyclic lifts with a new search core.

Parent start (H(3) or K_{d,d}) is kept as the fallback. The C engine is rewritten:
- Groups are generated inside C as permutation groups on P^1(GF(q)): PSL(2,p), PGL(2,p) for
  p in {5,7,11,13}, PSL(2,8) (GF(8) arithmetic), each optionally times Z_k, plus random
  semidirect products Z_m x| Z_k.
- Lifts range over base multigraphs with p <= 4 fibres per side, with the window extended up to
  the Moore bound (the parent's window excluded 1320-vertex PSL(2,11) lifts).
- The objective is the orbit-reduced excess distance, minimised by annealing with reheats.
- Every accepted lift is re-checked by the full bitset diameter test.
If no lift beats the start graph, the start graph is returned, so every case stays valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Lift search over explicit finite groups for bipartite degree-diameter graphs.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found (or the start graph).
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
#define MAXG 1100
#define MAXP 4
#define HS 8192
#define NFAM 7
#define KICK_AFTER 800
#define MAXPOOL 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;
typedef struct { unsigned char p[16]; } Perm;
typedef struct { int f, k, p; } Cand;
typedef struct { int ord; int *tab; } Fam;

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

/* Number of unordered pairs at distance > D, by bitsets. */
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
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
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

/* ---------------------------------------------------------------- finite fields */
static int QF;
static int FADD[16][16], FMUL[16][16], FINV[16], FNEG[16];

static void build_field(int q) {
    QF = q;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            if (q == 8) {
                FADD[a][b] = a ^ b;
                int r = 0;
                for (int i = 0; i < 3; i++)
                    if ((b >> i) & 1) r ^= a << i;
                for (int i = 4; i >= 3; i--)
                    if ((r >> i) & 1) r ^= 0xB << (i - 3);
                FMUL[a][b] = r;
            } else {
                FADD[a][b] = (a + b) % q;
                FMUL[a][b] = (a * b) % q;
            }
        }
    for (int a = 0; a < q; a++) {
        FINV[a] = 0;
        FNEG[a] = 0;
        for (int b = 0; b < q; b++) {
            if (FADD[a][b] == 0) FNEG[a] = b;
            if (a && FMUL[a][b] == 1) FINV[a] = b;
        }
    }
}

static int find_alpha(int q) {
    if (q == 8) return 2;
    for (int g = 2; g < q; g++) {
        int x = 1, ord = 0;
        do { x = FMUL[x][g]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) return g;
    }
    return 1;
}

/* ---------------------------------------------------------------- permutation groups on P^1(GF(q)) */
static uint64_t HK[HS];
static int HV[HS];
static Perm ELEM[MAXG];

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}
static uint64_t pkey(const Perm *P) {
    uint64_t k = 0;
    for (int i = 0; i <= QF; i++) k |= (uint64_t)P->p[i] << (4 * i);
    return k;
}
static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (HV[h]) {
        if (HK[h] == key) return HV[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}
static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (HV[h]) h = (h + 1) & (HS - 1);
    HK[h] = key;
    HV[h] = idx + 1;
}

/* Generators of PSL(2,q) (pgl = 0) or PGL(2,q); INF = q. For q = 8 PGL = PSL. */
static int gen_perms(int pgl, Perm *gen) {
    int INF = QF, ng = 0, al = find_alpha(QF);
    memset(gen, 0, sizeof(Perm) * 3);
    for (int x = 0; x <= QF; x++)
        gen[0].p[x] = (unsigned char)(x == INF ? INF : FADD[x][1 % QF]);
    ng = 1;
    for (int x = 0; x <= QF; x++) {
        int v;
        if (x == INF) v = 0;
        else if (x == 0) v = INF;
        else v = FNEG[FINV[x]];
        gen[1].p[x] = (unsigned char)v;
    }
    ng = 2;
    if (pgl || QF == 8) {
        for (int x = 0; x <= QF; x++)
            gen[2].p[x] = (unsigned char)(x == INF ? INF : FMUL[x][al]);
        ng = 3;
    }
    return ng;
}

static int closure_group(int pgl, int *ordp) {
    Perm gen[3];
    int ng = gen_perms(pgl, gen);
    memset(HV, 0, sizeof HV);
    memset(&ELEM[0], 0, sizeof(Perm));
    for (int x = 0; x <= QF; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(&ELEM[0]), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++)
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x <= QF; x++) h.p[x] = ELEM[qi].p[gen[k].p[x]];
            uint64_t key = pkey(&h);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    *ordp = n;
    return 1;
}

static int *build_table(int ord) {
    int *tab = malloc(sizeof(int) * (size_t)ord * (size_t)ord);
    if (!tab) return NULL;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x <= QF; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(&h));
            if (idx < 0) { free(tab); return NULL; }
            tab[(size_t)i * ord + j] = idx;
        }
    return tab;
}

static Fam FAM[NFAM];
static int nfam = 0;

static void init_families(void) {
    static const int QS[NFAM] = {5, 5, 7, 7, 8, 11, 13};
    static const int PG[NFAM] = {0, 1, 0, 1, 0, 0, 0};
    nfam = 0;
    for (int f = 0; f < NFAM; f++) {
        build_field(QS[f]);
        int ord = 0;
        if (!closure_group(PG[f], &ord)) continue;
        int *tab = build_table(ord);
        if (!tab) continue;
        FAM[nfam].ord = ord;
        FAM[nfam].tab = tab;
        nfam++;
    }
}

/* ---------------------------------------------------------------- current group */
static int GN;
static int GT[MAXG * MAXG];   /* GT[x*GN+y] = x*y, identity 0 */

/* Direct product of explicit family f with Z_k. */
static void set_group_explicit(int f, int k) {
    int o = FAM[f].ord, N = o * k;
    const int *t = FAM[f].tab;
    GN = N;
    for (int x = 0; x < o; x++)
        for (int c = 0; c < k; c++)
            for (int y = 0; y < o; y++)
                for (int e = 0; e < k; e++)
                    GT[(x * k + c) * N + (y * k + e)] = t[x * o + y] * k + (c + e) % k;
}

/* Random semidirect product Z_m x|_r Z_k with m*k = N. */
static int random_semidirect(int N) {
    for (int tries = 0; tries < 200; tries++) {
        int m = 1 + rndint(N);
        if (N % m) continue;
        int k = N / m;
        int r = 0;
        if (m > 1) {
            r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1) continue;
        }
        if (powmod(r, k, m) != 1 % m) continue;
        int rp[MAXG];
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
        GN = N;
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                GT[x * N + y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
            }
        }
        return 1;
    }
    return 0;
}

/* ---------------------------------------------------------------- voltage lifts */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1), s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
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

/* A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced excess distance. Left multiplication is an automorphism of the lift, so
 * BFS from the identity of each of the 2p fibres suffices. Each vertex at distance > D costs
 * dist - D, and each unreachable vertex costs 2. The total is zero iff the diameter is <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_excess(const Graph *g, int p) {
    int N = GN, nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * N;
        for (int v = 0; v < nv; v++) dist_buf[v] = -1;
        int head = 0, tail = 0;
        dist_buf[src] = 0;
        queue_buf[tail++] = src;
        while (head < tail) {
            int v = queue_buf[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (dist_buf[u] < 0) {
                    dist_buf[u] = dist_buf[v] + 1;
                    queue_buf[tail++] = u;
                }
            }
        }
        for (int v = 0; v < nv; v++) {
            if (dist_buf[v] < 0) total += 2;
            else if (dist_buf[v] > D) total += dist_buf[v] - D;
        }
    }
    return total;
}

/* Simulated annealing over the voltages of one random base multigraph on p + p fibres. */
static long lift_sa(Graph *g, int p, long steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP], bdt[MAXD * MAXP];
    int nd = 0, N = GN;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = (c == 0) ? rndint(N) : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, dt, nd);
    long cur = orbit_excess(g, p), best = cur, start = cur;
    memcpy(bdt, dt, sizeof(Dart) * nd);
    double T0 = 2.0 + 0.02 * (double)start, T = T0;
    long stall = 0;
    for (long s = 0; s < steps && best > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd), old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, dt, nd);
        long nv = orbit_excess(g, p);
        long delta = nv - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = nv;
        else dt[t].g = old;
        if (cur < best) {
            best = cur;
            memcpy(bdt, dt, sizeof(Dart) * nd);
            stall = 0;
        } else {
            stall++;
        }
        T *= 0.999;
        if (T < 0.5) T = 0.5;
        if (stall > KICK_AFTER && best > 0) {
            memcpy(dt, bdt, sizeof(Dart) * nd);
            for (int k = 0; k < 2; k++) {
                int u = rndint(nd);
                dt[u].g = fresh_voltage(dt, nd, u, dt[u].i, dt[u].j, N);
            }
            build_lift(g, p, dt, nd);
            cur = orbit_excess(g, p);
            T = T0;
            stall = 0;
        }
    }
    memcpy(dt, bdt, sizeof(Dart) * nd);
    build_lift(g, p, dt, nd);
    return best;
}

static int try_lift(Graph *best, Graph *cand, int p, double until) {
    double dl = now() + 3.0;
    if (dl > until) dl = until;
    for (int a = 0; a < 4 && now() < dl; a++) {
        long r = lift_sa(cand, p, 20000, dl);
        if (r == 0 && is_valid(cand) && cand->n > best->n) {
            copy_graph(best, cand);
            return 1;
        }
    }
    return 0;
}

static Cand POOL[MAXPOOL];

static int collect(long lo, long hi) {
    int np = 0;
    for (int f = 0; f < nfam; f++)
        for (int p = 1; p <= MAXP; p++)
            for (int k = 1;; k++) {
                long o = FAM[f].ord;
                long nv = 2L * p * o * k;
                if (o * k > MAXG || nv > hi) break;
                if (nv >= lo && np < MAXPOOL) {
                    POOL[np].f = f;
                    POOL[np].k = k;
                    POOL[np].p = p;
                    np++;
                }
            }
    return np;
}

static void search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long target = best->n + 2;
        if (target > moore) return;
        long hi = target + 160;
        if (hi > moore) hi = moore;
        int np = collect(target, hi);
        if (np == 0) np = collect(target, moore);
        if (np > 0 && rndint(4) != 0) {
            Cand c = POOL[rndint(np)];
            set_group_explicit(c.f, c.k);
            try_lift(best, &cand, c.p, until);
        } else {
            int p = 1 + rndint(MAXP);
            long Nmin = (target + 2L * p - 1) / (2L * p);
            long N = Nmin + rndint(60);
            if (2L * p * N > moore || N > MAXG || N < d) continue;
            if (!random_semidirect((int)N)) continue;
            try_lift(best, &cand, p, until);
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
    t_end = t0 + limit * 0.94;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { d = 1; D = 1; best.n = 0; }
    read_start(&best);
    if (best.n == 0 && d >= 1 && d <= MAXD) complete_bipartite(&best);
    if (best.n == 0) { best.n = 2; best.deg[0] = best.deg[1] = 0; best.side[0] = 0; best.side[1] = 1; add_edge(&best, 0, 1); }

    if (d >= 2 && D >= 2 && best.n < moore_bound()) {
        init_families();
        search(&best, t_end);
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
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Several sign conventions are tried; a candidate is kept only if it passes lib.is_valid.
    Returns None if nothing verifies.
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

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 4.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass
    return best
