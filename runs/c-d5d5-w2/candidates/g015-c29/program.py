"""Combined program: known constructions as a start, then a C engine that searches
bi-Cayley lifts over two group families and extends the best graph by grow-by-two annealing.

Bold change: lift search now also draws from non-abelian matrix groups
Z_p^2 x|_M Z_g2 (M in GL(2,p), M^g2 = I, p in {3,5,7}), not only the metacyclic
groups Z_m x| Z_k2. The lift search uses simulated annealing instead of a
near-greedy hill-climb. Grow-by-two still extends the best graph with the remaining time.
The best valid graph found so far is always kept, with K_{d,d} as the floor.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over groups G of order N with k vertices per side.
 *   A_{i,x} ~ B_{j,x*s} for each dart (i,j,s). Left multiplication is an automorphism,
 *   so diameter <= D is checked by BFS from the 2k representatives only.
 *   Groups: metacyclic Z_m x| Z_k2, or Z_p^2 x|_M Z_g2 with M^g2 = I over Z_p.
 *   Simulated annealing on the darts. Phase 1 stops early when it stalls.
 * Phase 2 (grow by two): add one vertex per side using stolen edges, then anneal
 *   degree-preserving swaps until the diameter bound holds. Targeted repair: each move
 *   starts at a vertex that currently has violating pairs.
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
#define MAXG 1024
#define MAXK 4
#define MAXC 40000

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;
static long moore;

/* ------------------------------------------------------------------ utilities */

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

static long compute_moore(void) {
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

/* ------------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Bitset reachability, D rounds.
   Also fills badv[v] = number of vertices at distance > D from v. */
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

/* Full validity: simple, bipartite by side labels, degree <= d, diameter <= D. */
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

/* ------------------------------------------------------------------ input / output */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------------ groups */

/* Multiplication table MT[x*N+y] = x*y for the current group of order N.
   Elements are coded x = a*K+b with a in the normal part, b in the cyclic part. */
static int RP[MAXG];
static int MT[MAXG * MAXG];

/* Metacyclic Z_m x|_r Z_k2: (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int set_group(int N, int m, int k2, int r) {
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < N; y++) {
            int c = y / k2, e = y % k2;
            MT[x * N + y] = (int)(((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
    return N;
}

/* Uniform random metacyclic group of order N, gcd(r,m) = 1, r^k2 = 1 mod m. */
static void random_group(int N) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k2 = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k2, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k2; br = r; }
        }
    }
    set_group(N, bm, bk, br);
}

/* Matrix groups Z_p^2 x|_M Z_g2: element (v,b), v in Z_p^2, b in Z_g2, coded
   x = (v0*p + v1)*g2 + b. (v,b)(w,c) = (v + M^b w, b+c mod g2). Needs M^g2 = I. */
typedef struct { unsigned short p, g2; unsigned char a, b, c, e; } MCand;
static MCand mcand[MAXC];
static int nmc = 0;

static void init_matrix_candidates(void) {
    static const int ps[3] = {3, 5, 7};
    nmc = 0;
    for (int pi = 0; pi < 3; pi++) {
        int p = ps[pi];
        for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
        for (int c = 0; c < p; c++)
        for (int e = 0; e < p; e++) {
            if (((a * e - b * c) % p + p) % p == 0) continue;
            int cur[4] = {1, 0, 0, 1};
            int ord = 0;
            for (int t = 1; t <= 48 && !ord; t++) {
                int n0 = (cur[0] * a + cur[1] * c) % p;
                int n1 = (cur[0] * b + cur[1] * e) % p;
                int n2 = (cur[2] * a + cur[3] * c) % p;
                int n3 = (cur[2] * b + cur[3] * e) % p;
                cur[0] = n0; cur[1] = n1; cur[2] = n2; cur[3] = n3;
                if (cur[0] == 1 && cur[1] == 0 && cur[2] == 0 && cur[3] == 1) ord = t;
            }
            if (!ord) continue;
            for (int g2 = 2; g2 <= 12; g2++) {
                if (g2 % ord) continue;
                if (p * p * g2 > MAXG || nmc >= MAXC) continue;
                mcand[nmc].p = (unsigned short)p;
                mcand[nmc].g2 = (unsigned short)g2;
                mcand[nmc].a = (unsigned char)a;
                mcand[nmc].b = (unsigned char)b;
                mcand[nmc].c = (unsigned char)c;
                mcand[nmc].e = (unsigned char)e;
                nmc++;
            }
        }
    }
}

static int set_matrix_group(const MCand *mc) {
    int p = mc->p, g2 = mc->g2;
    int N = p * p * g2;
    int M[4] = {mc->a, mc->b, mc->c, mc->e};
    static int PM[16][4];
    PM[0][0] = 1 % p; PM[0][1] = 0; PM[0][2] = 0; PM[0][3] = 1 % p;
    for (int b = 1; b < g2; b++) {
        const int *Q = PM[b - 1];
        int *R = PM[b];
        R[0] = (Q[0] * M[0] + Q[1] * M[2]) % p;
        R[1] = (Q[0] * M[1] + Q[1] * M[3]) % p;
        R[2] = (Q[2] * M[0] + Q[3] * M[2]) % p;
        R[3] = (Q[2] * M[1] + Q[3] * M[3]) % p;
    }
    for (int x = 0; x < N; x++) {
        int v = x / g2, b = x % g2;
        int v0 = v / p, v1 = v % p;
        const int *P = PM[b];
        for (int y = 0; y < N; y++) {
            int w = y / g2, c = y % g2;
            int w0 = w / p, w1 = w % p;
            int u0 = (P[0] * w0 + P[1] * w1) % p;
            int u1 = (P[2] * w0 + P[3] * w1) % p;
            int r0 = (v0 + u0) % p, r1 = (v1 + u1) % p;
            MT[x * N + y] = (r0 * p + r1) * g2 + (b + c) % g2;
        }
    }
    return N;
}

/* Pick a random matrix group whose order lies in [lo, hi]; returns its order or 0. */
static int pick_matrix_group(int lo, int hi) {
    static int cand[MAXC];
    int cnt = 0;
    for (int i = 0; i < nmc; i++) {
        int N = mcand[i].p * mcand[i].p * mcand[i].g2;
        if (N >= lo && N <= hi) cand[cnt++] = i;
    }
    if (cnt == 0) return 0;
    return set_matrix_group(&mcand[cand[rndint(cnt)]]);
}

/* ------------------------------------------------------------------ lifts */

static int K_, N_;          /* k vertices per side, group order */
static int nd_;             /* number of darts = d * k */
static int dI[MAXD * MAXK], dJ[MAXD * MAXK], dS[MAXD * MAXK];

static int adjL[MAXN][MAXD];
static int degL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int k = K_, N = N_, n = 2 * k * N;
    long pen = 0;
    for (int t = 0; t < nd_; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dS[t] == dS[u]) pen++;
    for (int v = 0; v < n; v++) degL[v] = 0;
    for (int t = 0; t < nd_; t++)
        for (int g = 0; g < N; g++) {
            int a = dI[t] * N + g;
            int b = (k + dJ[t]) * N + MT[g * N + dS[t]];
            adjL[a][degL[a]++] = b;
            adjL[b][degL[b]++] = a;
        }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < k; i++) reps[nr++] = i * N;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * N;
    for (int r = 0; r < nr; r++) {
        stampL++;
        int head = 0, tail = 0;
        int src = reps[r];
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < degL[u]; i++) {
                    int v = adjL[u][i];
                    if (visL[v] != stampL) { visL[v] = stampL; qL[tail++] = v; }
                }
            }
        }
        unreached += n - tail;
    }
    return pen * 1000000L + unreached;
}

static void build_lift(Graph *g) {
    int k = K_, N = N_;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (k + dJ[t]) * N + MT[x * N + dS[t]]);
}

/* Simulated annealing on the darts of a fresh random lift. Returns 1 if cost reaches 0. */
static int lift_attempt(int steps, double until) {
    int k = K_, N = N_;
    nd_ = d * k;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < k; i++) {
            int t = l * k + i;
            dI[t] = i;
            dJ[t] = perm[i];
            dS[t] = rndint(N);
        }
    }
    long c = lift_cost();
    const double T0 = 2.0;
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        double T = T0 * (1.0 - (double)s / steps) + 0.05;
        if (k > 1 && rnd01() < 0.15) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(nd_);
            int old = dS[t];
            dS[t] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

static Graph best;

/* Random lifts over metacyclic and matrix groups. Stops at `until`, or early once no
   improvement has come for half of the window: then the time is better spent growing `best`. */
static void lift_phase(double until) {
    static Graph cand;
    static const int kc[7] = {1, 1, 2, 2, 2, 3, 4};
    double start = now();
    double stall = 0.5 * (until - start);
    double last_gain = start;
    int fails = 0;
    while (now() < until && best.n < moore) {
        if (now() - last_gain > stall) return;
        int k = kc[rndint(7)];
        int target = best.n + 2;
        int need = (target + 2 * k - 1) / (2 * k);   /* minimum group order */
        int N = 0;
        if (nmc > 0 && rnd01() < 0.6)
            N = pick_matrix_group(need, need + need / 2 + 2);
        if (N == 0) {
            int Nl = need + rndint(3);
            if (Nl < 1 || Nl > MAXG) {
                if (++fails > 5000) return;
                continue;
            }
            N = Nl;
            random_group(N);
        }
        if (2 * k * N > moore || 2 * k * N > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        K_ = k;
        N_ = N;
        if (lift_attempt(40000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                last_gain = now();
            }
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

static int curbad[MAXN];
static int badlist[MAXN];

static int grow_once(const Graph *base, Graph *work, double until) {
    int n = base->n;
    if (n + 2 > moore || n + 2 > MAXN) return 0;
    copy_graph(work, base);
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
    int k = 0;
    for (int tries = 0; k < d - 1 && tries < 100000; tries++) {
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
    memcpy(curbad, badv, sizeof(int) * work->n);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int nbl = 0;
        for (int w = 0; w < work->n; w++)
            if (curbad[w] > 0) badlist[nbl++] = w;
        if (nbl == 0) break;
        int v = badlist[rndint(nbl)];
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
            memcpy(curbad, badv, sizeof(int) * work->n);
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
    static Graph work;
    while (now() < until && best.n + 2 <= moore) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(&best, &work, now() + slice)) copy_graph(&best, &work);
    }
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        init_matrix_candidates();
        /* Lift search gets up to 70% of the budget and stops early on stall;
           grow-by-two takes whatever time remains. */
        lift_phase(t0 + (t_end - t0) * 0.7);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Give C nearly the whole case budget; its own clock covers 95% of this value.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
