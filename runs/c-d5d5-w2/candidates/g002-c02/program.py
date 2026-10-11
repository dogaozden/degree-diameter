"""Combined program: known constructions as a start, then a C engine that searches
bi-Cayley lifts (voltage graphs) over two families of groups: metacyclic Z_m x| Z_k
and non-metacyclic matrix groups PGL(2,p) / PSL(2,p) (p = 3, 5, 7) times a cyclic
factor Z_c. The matrix-group family is the new idea: its groups have no metacyclic
structure, and records such as 336 = 2 * |PSL(2,7)| suggest that such groups are
where the good lifts live. Unused lift time goes to grow-by-two annealing."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over a group G with k vertices per side.
 *   A_{i,g} ~ B_{j,g*s} for each dart (i,j,s). Left multiplication is an automorphism,
 *   so diameter <= D is checked by BFS from the 2k representatives only.
 *   Groups come from two families:
 *     (a) metacyclic Z_m x|_r Z_k2 (formula multiplication);
 *     (b) NEW: PGL(2,p) or PSL(2,p) for p in {3,5,7}, times Z_c. Elements are
 *         normalised 2x2 matrices over Z_p, so the group is given by an explicit
 *         multiplication table.
 *   Hill-climb on voltages (and on the layer permutations when k > 1).
 *   Phase 1 stops early when it stalls, handing the remaining time to phase 2.
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
#define MAXBASE 512
#define MAXCAT 128

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
    if (b < 0) b += m;
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

/* ------------------------------------------------------------------ group tables */

/* Current group multiplication table: MT[x*N+y] = x*y, identity = index 0. */
static int N_;              /* group order of the current lift */
static int K_;              /* k vertices per side */
static int MT[MAXG * MAXG];

/* Metacyclic family: Z_m x|_r Z_k2, element (a,b) = a*k2+b,
   (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int RP[MAXG];

static void set_group(int N, int m, int k2, int r) {
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    N_ = N;
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

/* ---- Matrix-group family (new): PGL(2,p) or PSL(2,p) over Z_p, times Z_c.
   Elements are 2x2 matrices scaled so that the first nonzero entry is 1.
   PSL(2,p) = matrices whose determinant is a square (well defined on the
   projective class), so it is the index-2 subgroup of PGL(2,p). */

static int BP = 0, BPSL = 0, BN = 0;
static int BM[MAXBASE][4];
static int BT[MAXBASE * MAXBASE];
static int CODEIDX[4096];

typedef struct { int p, psl, c, N; } CatEnt;
static CatEnt cat[MAXCAT];
static int ncat = 0;

static int md(long x, int p) {
    x %= p;
    return (int)(x < 0 ? x + p : x);
}

static int inv_mod(int x, int p) { return (int)powmod(x, p - 2, p); }

/* Scale a nonzero matrix so that its first nonzero entry becomes 1. */
static void normalise(int *m, int p) {
    for (int i = 0; i < 4; i++)
        if (m[i]) {
            int s = inv_mod(m[i], p);
            for (int j = 0; j < 4; j++) m[j] = md((long)m[j] * s, p);
            return;
        }
}

static int mcode(const int *m, int p) { return ((m[0] * p + m[1]) * p + m[2]) * p + m[3]; }

/* Build the base group (PGL or PSL) for prime p; identity gets index 0.
   Returns its order. Cached on (p, psl). */
static int build_base(int p, int psl) {
    if (p == BP && psl == BPSL && BN > 0) return BN;
    BP = p;
    BPSL = psl;
    for (int i = 0; i < p * p * p * p; i++) CODEIDX[i] = -1;
    int id[4] = {1, 0, 0, 1};
    memcpy(BM[0], id, sizeof id);
    CODEIDX[mcode(id, p)] = 0;
    BN = 1;
    for (int a = 0; a < p; a++)
        for (int b = 0; b < p; b++)
            for (int c = 0; c < p; c++)
                for (int e = 0; e < p; e++) {
                    int m[4] = {a, b, c, e};
                    int first = -1;
                    for (int i = 0; i < 4; i++)
                        if (m[i]) { first = i; break; }
                    if (first < 0 || m[first] != 1) continue;   /* not canonical */
                    if (CODEIDX[mcode(m, p)] != -1) continue;
                    int det = md((long)a * e - (long)b * c, p);
                    if (det == 0) continue;
                    if (psl && powmod(det, (p - 1) / 2, p) != 1) continue;
                    if (BN >= MAXBASE) continue;
                    CODEIDX[mcode(m, p)] = BN;
                    memcpy(BM[BN], m, sizeof m);
                    BN++;
                }
    for (int x = 0; x < BN; x++)
        for (int y = 0; y < BN; y++) {
            const int *A = BM[x], *B = BM[y];
            int r[4];
            r[0] = md((long)A[0] * B[0] + (long)A[1] * B[2], p);
            r[1] = md((long)A[0] * B[1] + (long)A[1] * B[3], p);
            r[2] = md((long)A[2] * B[0] + (long)A[3] * B[2], p);
            r[3] = md((long)A[2] * B[1] + (long)A[3] * B[3], p);
            normalise(r, p);
            int c = CODEIDX[mcode(r, p)];
            BT[x * BN + y] = c < 0 ? 0 : c;   /* the set is closed under products */
        }
    return BN;
}

static void build_catalog(void) {
    static const int ps[3] = {3, 5, 7};
    ncat = 0;
    for (int pi = 0; pi < 3; pi++)
        for (int psl = 0; psl < 2; psl++)
            for (int c = 1; c <= 16; c++) {
                int p = ps[pi];
                long B = (long)p * (p * p - 1);
                if (psl) B /= 2;
                long N = B * c;
                if (N < 2 || N > MAXG || N > moore || ncat >= MAXCAT) continue;
                cat[ncat].p = p;
                cat[ncat].psl = psl;
                cat[ncat].c = c;
                cat[ncat].N = (int)N;
                ncat++;
            }
}

/* Install the table of catalog group e (base x Z_c) as the current group. */
static void set_table_group(const CatEnt *e) {
    int B = build_base(e->p, e->psl);
    int c = e->c, N = B * c;
    N_ = N;
    for (int x = 0; x < N; x++) {
        int g1 = x / c, z1 = x % c;
        for (int y = 0; y < N; y++) {
            int g2 = y / c, z2 = y % c;
            MT[x * N + y] = BT[g1 * B + g2] * c + (z1 + z2) % c;
        }
    }
}

/* Random catalog group whose k-lift has between target and moore vertices. */
static int pick_catalog(int k, long target) {
    static int idx[MAXCAT];
    int ne = 0;
    for (int i = 0; i < ncat; i++) {
        long vn = 2L * k * cat[i].N;
        if (vn >= target && vn <= moore && vn <= MAXN) idx[ne++] = i;
    }
    return ne ? idx[rndint(ne)] : -1;
}

/* ------------------------------------------------------------------ lifts */

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

/* Hill-climb on the darts of a fresh random lift (group already installed).
   Returns 1 if cost reaches 0. */
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

/* Lift search over both group families. Stops at `until`, or early once no
   improvement has come for half of the window: then the time is better spent
   growing `best`. */
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
        int ci = (rndint(2) == 0) ? pick_catalog(k, target) : -1;
        if (ci >= 0) {
            K_ = k;
            set_table_group(&cat[ci]);      /* NEW: PGL/PSL(2,p) x Z_c */
        } else {
            long Nl = (target + 2 * k - 1) / (2 * k) + rndint(3);
            if (Nl < 1 || Nl > MAXG || 2 * k * Nl > moore || 2 * k * Nl > MAXN) {
                if (++fails > 5000) return;
                continue;
            }
            K_ = k;
            random_group((int)Nl);          /* metacyclic */
        }
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
    build_catalog();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        lift_phase(t0 + (t_end - t0) * 0.75);
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

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
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
