"""Cayley-lift search over non-metabelian groups, with the parent engine as fallback.

Phase A (bold change): bipartite Cayley graphs A_g ~ B_{g s} (s in S, |S| = d) over
matrix groups that the parent's semidirect-product lifts cannot produce: PGL(2,p),
PSL(2,p), SL(2,p) and ASL(2,p) = Z_p^2 x| SL(2,p). Every candidate with 2|G| > current
best and 2|G| <= Moore bound is tried, largest first. The C core fixes the identity in S
(WLOG by the automorphisms A_g -> A_{g a}, B_x -> B_{x b}) and anneals over the other
d-1 elements. Cost = unreached (vertex, representative) pairs from A_e and B_e, which is
zero iff the diameter bound holds, because left multiplication is an automorphism.

Phase B (safe fallback): the parent's semidirect-lift engine gets the remaining time and
grows whatever graph phase A produced. Every returned graph is checked with lib.is_valid,
and the answer falls back to K_{d,d} or the known construction if anything fails.
"""
import time

import lib

CAY_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1024
#define MAXV (2 * MAXG)
#define MAXD 32
#define EPOCH 40000

/* type: 0 = PGL(2,p), 1 = PSL(2,p), 2 = SL(2,p), 3 = ASL(2,p) (affine SL). */
static int TYPE, P, L, D, d, N, ident;
static int *idx_of, *code_of;
static int mul[MAXG][MAXG];
static int inv_[MAXG];
static int S[MAXD], SI[MAXD];
static int stampv[MAXV], qv[MAXV];
static int stc = 0;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 1;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int md(long x) {
    x %= P;
    if (x < 0) x += P;
    return (int)x;
}

static int inv_p(int a) {
    long r = 1, b = a % P, e = P - 2;
    while (e > 0) {
        if (e & 1) r = r * b % P;
        b = b * b % P;
        e >>= 1;
    }
    return (int)r;
}

static void decode(int code, int *e) {
    for (int k = 0; k < L; k++) {
        e[k] = code % P;
        code /= P;
    }
}

static int encode(const int *e) {
    int c = 0;
    for (int k = L - 1; k >= 0; k--) c = c * P + e[k];
    return c;
}

static int det2(const int *e) { return md((long)e[0] * e[3] - (long)e[1] * e[2]); }

static int is_square(int x) {
    for (int y = 0; y < P; y++)
        if (y * y % P == x) return 1;
    return 0;
}

/* Projective normalisation: first nonzero entry becomes 1. */
static void normalize2(int *e) {
    int k = 0;
    while (k < 4 && e[k] == 0) k++;
    if (k == 4 || e[k] == 1) return;
    int iv = inv_p(e[k]);
    for (int j = 0; j < 4; j++) e[j] = md((long)e[j] * iv);
}

static int member(int code) {
    int e[6];
    decode(code, e);
    if (TYPE <= 2) {
        int det = det2(e);
        if (TYPE == 2) return det == 1;
        if (det == 0) return 0;
        int k = 0;
        while (e[k] == 0) k++;
        if (e[k] != 1) return 0;
        if (TYPE == 1) return is_square(det);
        return 1;
    }
    return det2(e + 2) == 1;
}

static int product(int ca, int cb) {
    int a[6], b[6], c[6];
    decode(ca, a);
    decode(cb, b);
    if (TYPE <= 2) {
        c[0] = md((long)a[0] * b[0] + (long)a[1] * b[2]);
        c[1] = md((long)a[0] * b[1] + (long)a[1] * b[3]);
        c[2] = md((long)a[2] * b[0] + (long)a[3] * b[2]);
        c[3] = md((long)a[2] * b[1] + (long)a[3] * b[3]);
        if (TYPE <= 1) normalize2(c);
        return encode(c);
    }
    /* (v,M)(w,K) = (v + M w, M K); v = a[0..1], M = a[2..5] row-major. */
    c[0] = md((long)a[0] + (long)a[2] * b[0] + (long)a[3] * b[1]);
    c[1] = md((long)a[1] + (long)a[4] * b[0] + (long)a[5] * b[1]);
    c[2] = md((long)a[2] * b[2] + (long)a[3] * b[4]);
    c[3] = md((long)a[2] * b[3] + (long)a[3] * b[5]);
    c[4] = md((long)a[4] * b[2] + (long)a[5] * b[4]);
    c[5] = md((long)a[4] * b[3] + (long)a[5] * b[5]);
    return encode(c);
}

static int build_group(int type, int p) {
    TYPE = type;
    P = p;
    L = (type == 3) ? 6 : 4;
    int CS = 1;
    for (int k = 0; k < L; k++) CS *= P;
    idx_of = malloc(sizeof(int) * (size_t)CS);
    code_of = malloc(sizeof(int) * MAXG);
    if (!idx_of || !code_of) return 0;
    for (int c = 0; c < CS; c++) idx_of[c] = -1;
    N = 0;
    for (int c = 0; c < CS; c++) {
        if (!member(c)) continue;
        if (N >= MAXG) return 0;
        idx_of[c] = N;
        code_of[N++] = c;
    }
    int ie[6] = {0, 0, 0, 0, 0, 0};
    if (TYPE == 3) {
        ie[2] = 1;
        ie[5] = 1;
    } else {
        ie[0] = 1;
        ie[3] = 1;
    }
    ident = idx_of[encode(ie)];
    if (ident < 0) return 0;
    for (int i = 0; i < N; i++)
        for (int j = 0; j < N; j++) {
            int k = idx_of[product(code_of[i], code_of[j])];
            if (k < 0) return 0;
            mul[i][j] = k;
        }
    for (int i = 0; i < N; i++) {
        inv_[i] = -1;
        for (int j = 0; j < N; j++)
            if (mul[i][j] == ident) {
                inv_[i] = j;
                break;
            }
        if (inv_[i] < 0) return 0;
    }
    return 1;
}

static int in_S(int t, int upto) {
    for (int i = 0; i < upto; i++)
        if (S[i] == t) return 1;
    return 0;
}

/* Vertices: A_g = g (0..N-1), B_x = N + x. Edges A_g ~ B_{g s}, s in S. */
static int reach_count(int src) {
    stc++;
    int head = 0, tail = 0;
    qv[tail++] = src;
    stampv[src] = stc;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int u = qv[head++], v;
            if (u < N) {
                for (int i = 0; i < d; i++) {
                    v = N + mul[u][S[i]];
                    if (stampv[v] != stc) {
                        stampv[v] = stc;
                        qv[tail++] = v;
                    }
                }
            } else {
                int x = u - N;
                for (int i = 0; i < d; i++) {
                    v = mul[x][SI[i]];
                    if (stampv[v] != stc) {
                        stampv[v] = stc;
                        qv[tail++] = v;
                    }
                }
            }
        }
    }
    return tail;
}

/* Zero iff diameter <= D (both representatives reach everything within D). */
static int cost(void) {
    return (2 * N - reach_count(ident)) + (2 * N - reach_count(N + ident));
}

static int random_S(void) {
    S[0] = ident;
    SI[0] = inv_[ident];
    for (int i = 1; i < d; i++) {
        int t;
        do {
            t = rndint(N);
        } while (in_S(t, i));
        S[i] = t;
        SI[i] = inv_[t];
    }
    return cost();
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: %s d D seed time_limit type p\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int type = atoi(argv[5]);
    int p = atoi(argv[6]);
    double t_end = now() + limit * 0.9;
    rs = 0x9E3779B97F4A7C15ULL * (uint64_t)(seed + 7) ^ (uint64_t)(type * 131 + p);
    if (!rs) rs = 1;
    for (int i = 0; i < 8; i++) rnd();
    if (d < 2 || d > MAXD || D < 2 || p < 2 || type < 0 || type > 3 ||
        !build_group(type, p) || N < d) {
        printf("0 0\n");
        return 0;
    }

    double T0 = 2.0, T1 = 0.15;
    double decay = pow(T1 / T0, 1.0 / EPOCH);
    int found = 0;
    while (!found && now() < t_end) {
        int c = random_S();
        double T = T0;
        for (int it = 0; it < EPOCH && c > 0; it++) {
            if ((it & 255) == 0 && now() > t_end) break;
            int i = 1 + rndint(d - 1);
            int t = rndint(N);
            if (in_S(t, d)) continue;
            int old = S[i], oldsi = SI[i];
            S[i] = t;
            SI[i] = inv_[t];
            int c2 = cost();
            if (c2 <= c || rnd01() < exp((double)(c - c2) / T)) {
                c = c2;
            } else {
                S[i] = old;
                SI[i] = oldsi;
            }
            T *= decay;
        }
        if (c == 0) found = 1;
    }
    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + mul[g][S[i]]);
    return 0;
}
'''

# Parent engine (semidirect-product bi-Cayley lifts, then grow-by-two), kept as fallback.
OLD_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over groups Z_m x| Z_k2 with k vertices per side.
 *   A_{i,g} ~ B_{j,g*s} for each dart (i,j,s). Left multiplication is an automorphism,
 *   so diameter <= D is checked by BFS from the 2k representatives only.
 *   Hill-climb on voltages. Phase 1 stops early when it stalls.
 * Phase 2 (grow by two): add one vertex per side using stolen edges, then anneal
 *   degree-preserving swaps until the diameter bound holds.
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
#define MAXK 3

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

/* Number of unordered pairs at distance > D. Bitset reachability, D rounds. */
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

/* Z_m x|_r Z_k2: element (a,b) = a*k2+b; (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK, GR;
static int RP[MAXG];
static int MT[MAXG * MAXG];   /* MT[x*N+y] = x*y */

static void set_group(int N, int m, int k2, int r) {
    GM = m; GK = k2; GR = r;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k2, b = x % k2;
        for (int y = 0; y < N; y++) {
            int c = y / k2, e = y % k2;
            MT[x * N + y] = (int)(((long)a + (long)RP[b] * c) % m) * k2 + (b + e) % k2;
        }
    }
}

/* Uniform random (m, k2, r) with m*k2 = N, gcd(r,m) = 1, r^k2 = 1 mod m. */
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

/* Hill-climb on the darts of a fresh random lift. Returns 1 if cost reaches 0. */
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
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 255) == 0 && now() > until) break;
        if (k > 1 && rnd01() < 0.15) {
            int l = rndint(d), a = rndint(k), b = rndint(k);
            if (a == b) continue;
            int t1 = l * k + a, t2 = l * k + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(nd_);
            int old = dS[t];
            dS[t] = rndint(N);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < 0.01) c = c2;
            else dS[t] = old;
        }
    }
    return c == 0;
}

static Graph best;

/* Random lifts one group at a time. Stops at `until`, or early once no improvement
   has come for half of the window: then the time is better spent growing `best`. */
static void lift_phase(double until) {
    static Graph cand;
    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    double start = now();
    double stall = 0.5 * (until - start);
    double last_gain = start;
    int fails = 0;
    while (now() < until && best.n < moore) {
        if (now() - last_gain > stall) return;
        int k = kc[rndint(6)];
        long target = best.n + 2;
        long Nl = (target + 2 * k - 1) / (2 * k) + rndint(3);
        if (Nl < 1 || Nl > MAXG || 2 * k * Nl > moore || 2 * k * Nl > MAXN) {
            if (++fails > 5000) return;
            continue;
        }
        int N = (int)Nl;
        K_ = k;
        N_ = N;
        random_group(N);
        /* Deep hill-climb per random group: most lifts stall well above cost 0,
           so a longer search per group finds valid voltages where restarts do not. */
        if (lift_attempt(25000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) {
                copy_graph(&best, &cand);
                last_gain = now();
            }
        }
    }
}

/* ------------------------------------------------------------------ grow by two */

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
    t_end = t0 + limit * 0.9;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        /* Lift search gets up to 60% of the budget and stops early on stall;
           grow-by-two takes whatever time remains. */
        lift_phase(t0 + (t_end - t0) * 0.6);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

_CAY_PRIMES = (2, 3, 5, 7, 11, 13)


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def _cayley_candidates(moore, best_n):
    """(order, type, p) for matrix groups G with best_n < 2|G| <= moore, largest first."""
    out = []
    for p in _CAY_PRIMES:
        sl = p * (p * p - 1)
        for typ, order in ((0, sl), (1, sl // 2), (2, sl), (3, p * p * sl)):
            if typ == 1 and p == 2:
                continue  # PSL(2,2) = PGL(2,2), handled by type 0
            if best_n < 2 * order <= moore:
                out.append((order, typ, p))
    out.sort(reverse=True)
    return out


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

    def budget_left():
        return 0.85 * time_limit - 1.0 - (time.monotonic() - t0)

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or budget_left() < 1.0:
        return best

    # Phase A: bi-Cayley graphs over non-metabelian matrix groups.
    if d >= 2 and D >= 2:
        cay_end = time.monotonic() + 0.5 * budget_left()
        cands = _cayley_candidates(moore, best[0])
        for k, (order, typ, p) in enumerate(cands):
            if 2 * order <= best[0]:
                continue
            left = cay_end - time.monotonic()
            if left < 1.0:
                break
            share = left / (len(cands) - k)
            try:
                text = lib.run_c(CAY_SOURCE, [d, D, seed, round(share, 2), typ, p],
                                 timeout=share + 5)
                consider(lib.parse_graph_text(text))
            except (RuntimeError, ValueError):
                pass

    # Phase B: parent engine grows whatever phase A produced (safe fallback).
    left = budget_left()
    if left >= 2.0 and best[0] < moore:
        try:
            text = lib.run_c(OLD_SOURCE, [d, D, seed, round(left, 2)],
                             stdin_graph=best, timeout=left + 5)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
