"""Two-engine search for bipartite degree-diameter graphs.

Stage 1 runs the bi-Cayley lift search (the parent's engine). Stage 2 is a new
construction: Haar graphs Cay-bipartite(G, S) over non-metacyclic groups G built
from permutation generators (symmetric, alternating, PSL/PGL(2,p), AGL(1,p) and
direct products). A group of order N with connection set S of size d gives a
bipartite graph on 2N vertices, with a ~ b iff a^-1 b in S. Left and right
multiplication are automorphisms, so the diameter check needs only two BFS runs
(from left and right identities). Simulated annealing on S minimises the number of
unreached pairs. Every output is validated in C and again in Python before use.
"""
import time

import lib

LIFT_C = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): bi-Cayley lifts over groups Z_m x| Z_k2 with k vertices per side.
 *   A_{i,g} ~ B_{j,g*s} for each dart (i,j,s). Left multiplication is an automorphism,
 *   so diameter <= D is checked by BFS from the 2k representatives only.
 *   Hill-climb on voltages (and occasionally on the target matching of a layer).
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

static void lift_phase(double until) {
    static Graph cand;
    static const int kc[6] = {1, 1, 1, 2, 2, 3};
    int fails = 0;
    while (now() < until && best.n < moore) {
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
        /* Longer hill-climbs per random group: most lifts stall well above cost 0,
           so a deeper search per group finds valid voltages where restarts do not. */
        if (lift_attempt(25000, until)) {
            build_lift(&cand);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

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

HAAR_C = r'''
/* Haar-graph search over non-metacyclic groups.
 *
 * Usage:  prog d D seed time_limit min_n     (stdin is ignored)
 * Output: "n m" and m edges of a valid bipartite graph with n > min_n, or "0 0".
 *
 * Graph: left vertices a in G, right vertices b in G, a ~ b iff a^-1 b in S, |S| = d.
 * Left and right multiplication are automorphisms, so pair distances reduce to BFS
 * from the left identity and from the right identity. Cost = unreached pairs.
 * Groups come from permutation generators: S_n, A_n, PSL(2,p), PGL(2,p), AGL(1,p),
 * cyclic factors, and direct products of two factors.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXP 64
#define MAXGEN 8
#define MAXN 512
#define MAXD 16
#define HS 4096
#define MAXF 80
#define MAXCAND 4000

typedef struct {
    int deg;
    int ng;
    unsigned char gen[MAXGEN][MAXP];
} Spec;

typedef struct { int i, j, N; } Cand;

static int d, D;
static long moore;
static double t_end;

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
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

/* ------------------------------------------------------------------ permutation factors */

static void spec_cyc(Spec *s, int m) {
    memset(s, 0, sizeof *s);
    s->deg = m;
    s->ng = 1;
    for (int i = 0; i < m; i++) s->gen[0][i] = (unsigned char)((i + 1) % m);
}

static void spec_sym(Spec *s, int n) {
    memset(s, 0, sizeof *s);
    s->deg = n;
    s->ng = 2;
    for (int i = 0; i < n; i++) {
        s->gen[0][i] = (unsigned char)i;
        s->gen[1][i] = (unsigned char)((i + 1) % n);
    }
    s->gen[0][0] = 1;
    s->gen[0][1] = 0;
}

static void spec_alt(Spec *s, int n) {
    memset(s, 0, sizeof *s);
    s->deg = n;
    s->ng = n - 2;
    for (int g = 0; g < s->ng; g++) {
        int i = g + 2;
        for (int k = 0; k < n; k++) s->gen[g][k] = (unsigned char)k;
        s->gen[g][0] = 1;
        s->gen[g][1] = (unsigned char)i;
        s->gen[g][i] = 0;
    }
}

static int prim_root(int p) {
    for (int g = 2; g < p; g++) {
        int x = 1, ord = 0;
        do { x = x * g % p; ord++; } while (x != 1);
        if (ord == p - 1) return g;
    }
    return 1;
}

/* PSL(2,p) on the projective line (points 0..p-1, infinity = p); PGL if with_scalar. */
static void spec_pgl(Spec *s, int p, int with_scalar) {
    int deg = p + 1, INF = p;
    memset(s, 0, sizeof *s);
    s->deg = deg;
    s->ng = with_scalar ? 3 : 2;
    int g = prim_root(p);
    for (int x = 0; x < deg; x++) {
        s->gen[0][x] = (unsigned char)(x == INF ? INF : (x + 1) % p);
        int sv;
        if (x == INF) sv = 0;
        else if (x == 0) sv = INF;
        else sv = (int)((p - powmod(x, p - 2, p)) % p);
        s->gen[1][x] = (unsigned char)sv;
        if (with_scalar)
            s->gen[2][x] = (unsigned char)(x == INF ? INF : (x * g) % p);
    }
}

/* AGL(1,p) on Z_p. */
static void spec_agl(Spec *s, int p) {
    memset(s, 0, sizeof *s);
    s->deg = p;
    s->ng = 2;
    int g = prim_root(p);
    for (int x = 0; x < p; x++) {
        s->gen[0][x] = (unsigned char)((x + 1) % p);
        s->gen[1][x] = (unsigned char)((x * g) % p);
    }
}

/* Direct product on disjoint supports. */
static void spec_prod(Spec *r, const Spec *a, const Spec *b) {
    memset(r, 0, sizeof *r);
    r->deg = a->deg + b->deg;
    r->ng = a->ng + b->ng;
    for (int g = 0; g < a->ng; g++)
        for (int i = 0; i < r->deg; i++)
            r->gen[g][i] = (unsigned char)(i < a->deg ? a->gen[g][i] : i);
    for (int g = 0; g < b->ng; g++) {
        int G = a->ng + g;
        for (int i = 0; i < r->deg; i++)
            r->gen[G][i] = (unsigned char)(i < a->deg ? i : a->deg + b->gen[g][i - a->deg]);
    }
}

/* ------------------------------------------------------------------ group closure */

static unsigned char elem[MAXN][MAXP];
static int htab[HS];
static int MT[MAXN * MAXN];
static int INV[MAXN];
static int NG;

static uint32_t phash(const unsigned char *p, int P) {
    uint32_t h = 2166136261u;
    for (int i = 0; i < P; i++) {
        h ^= p[i];
        h *= 16777619u;
    }
    return h;
}

static int hfind(const unsigned char *p, int P) {
    uint32_t h = phash(p, P) & (HS - 1);
    while (htab[h]) {
        if (memcmp(elem[htab[h] - 1], p, (size_t)P) == 0) return htab[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(int idx, int P) {
    uint32_t h = phash(elem[idx], P) & (HS - 1);
    while (htab[h]) h = (h + 1) & (HS - 1);
    htab[h] = idx + 1;
}

/* Returns group order, or -1 if it exceeds limit. Element 0 is the identity. */
static int build_group(const Spec *s, int limit) {
    int P = s->deg;
    unsigned char tmp[MAXP];
    memset(htab, 0, sizeof htab);
    for (int i = 0; i < P; i++) elem[0][i] = (unsigned char)i;
    hput(0, P);
    int N = 1;
    for (int i = 0; i < N; i++) {
        for (int g = 0; g < s->ng; g++) {
            for (int k = 0; k < P; k++) tmp[k] = elem[i][s->gen[g][k]];
            if (hfind(tmp, P) < 0) {
                if (N >= limit) return -1;
                memcpy(elem[N], tmp, (size_t)P);
                hput(N, P);
                N++;
            }
        }
    }
    return N;
}

static int build_tables(int N, int P) {
    unsigned char tmp[MAXP];
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            for (int k = 0; k < P; k++) tmp[k] = elem[x][elem[y][k]];
            int idx = hfind(tmp, P);
            if (idx < 0) return 0;
            MT[x * N + y] = idx;
        }
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INV[x] = y; break; }
        if (INV[x] < 0) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------------ factors and candidates */

static Spec F[MAXF];
static int Fab[MAXF];
static int Fo[MAXF];
static int nF = 0;
static Cand cand[MAXCAND];
static int nc = 0;

static void add_factor(const Spec *s, int ab) {
    F[nF] = *s;
    Fab[nF] = ab;
    nF++;
}

static void init_factors(void) {
    Spec t;
    nF = 0;
    for (int m = 2; m <= 48; m++) { spec_cyc(&t, m); add_factor(&t, 1); }
    for (int n = 3; n <= 5; n++) { spec_sym(&t, n); add_factor(&t, 0); }
    for (int n = 4; n <= 5; n++) { spec_alt(&t, n); add_factor(&t, 0); }
    spec_pgl(&t, 5, 0); add_factor(&t, 0);
    spec_pgl(&t, 7, 0); add_factor(&t, 0);
    spec_pgl(&t, 5, 1); add_factor(&t, 0);
    spec_pgl(&t, 7, 1); add_factor(&t, 0);
    int ps[5] = {5, 7, 11, 13, 17};
    for (int i = 0; i < 5; i++) { spec_agl(&t, ps[i]); add_factor(&t, 0); }
    for (int i = 0; i < nF; i++) Fo[i] = build_group(&F[i], MAXN);
}

static void build_candidates(long lo, long hi) {
    nc = 0;
    for (int i = 0; i < nF; i++) {
        if (Fo[i] <= 0 || Fab[i]) continue;
        if (Fo[i] >= lo && Fo[i] <= hi && nc < MAXCAND) {
            cand[nc].i = i;
            cand[nc].j = -1;
            cand[nc].N = Fo[i];
            nc++;
        }
    }
    for (int i = 0; i < nF; i++)
        for (int j = i; j < nF; j++) {
            if (nc >= MAXCAND) break;
            if (Fo[i] <= 0 || Fo[j] <= 0) continue;
            if (Fab[i] && Fab[j]) continue;
            if (F[i].deg + F[j].deg > MAXP) continue;
            long N = (long)Fo[i] * (long)Fo[j];
            if (N < lo || N > hi) continue;
            cand[nc].i = i;
            cand[nc].j = j;
            cand[nc].N = (int)N;
            nc++;
        }
    for (int a = 1; a < nc; a++) {
        Cand x = cand[a];
        int b = a - 1;
        while (b >= 0 && cand[b].N < x.N) { cand[b + 1] = cand[b]; b--; }
        cand[b + 1] = x;
    }
}

/* ------------------------------------------------------------------ Haar search */

static int Sset[MAXD];
static unsigned char inS[MAXN];
static int vis[2 * MAXN], qq[2 * MAXN];
static int stampv = 0;

static int best_n = 0, best_m = 0;
static int be_u[MAXN * MAXD], be_v[MAXN * MAXD];
static int tu[MAXN * MAXD], tv[MAXN * MAXD];

/* Unreached (vertex, pair) count from the left identity plus from the right identity. */
static long eval_cost(void) {
    int N = NG;
    long cost = 0;
    for (int side = 0; side < 2; side++) {
        int src = side == 0 ? 0 : N;
        stampv++;
        if (stampv > 1000000000) { memset(vis, 0, sizeof vis); stampv = 1; }
        int head = 0, tail = 0;
        vis[src] = stampv;
        qq[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qq[head++];
                if (u < N) {
                    const int *row = MT + u * N;
                    for (int i = 0; i < d; i++) {
                        int v = N + row[Sset[i]];
                        if (vis[v] != stampv) { vis[v] = stampv; qq[tail++] = v; }
                    }
                } else {
                    const int *row = MT + (u - N) * N;
                    for (int i = 0; i < d; i++) {
                        int v = row[INV[Sset[i]]];
                        if (vis[v] != stampv) { vis[v] = stampv; qq[tail++] = v; }
                    }
                }
            }
        }
        cost += 2 * N - tail;
    }
    return cost;
}

static void random_S(void) {
    int N = NG;
    memset(inS, 0, (size_t)N);
    Sset[0] = 0;
    inS[0] = 1;
    for (int k = 1; k < d; k++) {
        int x;
        do { x = 1 + rndint(N - 1); } while (inS[x]);
        Sset[k] = x;
        inS[x] = 1;
    }
}

/* Simulated annealing with restarts. Returns 1 when cost 0 is reached before until. */
static int anneal(double until) {
    int N = NG;
    long cost;
    int it = 0;
    for (;;) {
        random_S();
        cost = eval_cost();
        double T = 1.0;
        long best_c = cost;
        long stagn = 0;
        while (cost > 0) {
            if ((++it & 127) == 0 && now() > until) return 0;
            int k = 1 + rndint(d - 1);
            int x = 1 + rndint(N - 1);
            if (inS[x]) continue;
            int old = Sset[k];
            inS[old] = 0;
            inS[x] = 1;
            Sset[k] = x;
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / T)) {
                cost = c2;
                if (cost < best_c) { best_c = cost; stagn = 0; }
                else stagn++;
            } else {
                inS[x] = 0;
                inS[old] = 1;
                Sset[k] = old;
                stagn++;
            }
            T *= 0.9995;
            if (T < 0.15) T = 0.15;
            if (stagn > 20000) break;
        }
        if (cost == 0) return 1;
        if (now() > until) return 0;
    }
}

/* Independent check of a produced graph: degrees, bipartition, diameter by BFS from all. */
static int full_check(int n, const int *eu, const int *ev, int m, int half) {
    static int adjF[2 * MAXN][MAXD];
    static int dg[2 * MAXN];
    static int seenF[2 * MAXN], qF[2 * MAXN];
    static int stampF = 0;
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = eu[e], v = ev[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if ((u < half) == (v < half)) return 0;
        if (dg[u] >= MAXD || dg[v] >= MAXD) return 0;
        adjF[u][dg[u]++] = v;
        adjF[v][dg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        if (dg[v] > d) return 0;
    for (int s = 0; s < n; s++) {
        stampF++;
        int head = 0, tail = 0;
        seenF[s] = stampF;
        qF[tail++] = s;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qF[head++];
                for (int i = 0; i < dg[u]; i++) {
                    int w = adjF[u][i];
                    if (seenF[w] != stampF) { seenF[w] = stampF; qF[tail++] = w; }
                }
            }
        }
        if (tail != n) return 0;
    }
    return 1;
}

static int store_graph(void) {
    int N = NG, n = 2 * N, m = 0;
    for (int a = 0; a < N; a++)
        for (int i = 0; i < d; i++) {
            tu[m] = a;
            tv[m] = N + MT[a * N + Sset[i]];
            m++;
        }
    if (n <= best_n) return 0;
    if (!full_check(n, tu, tv, m, N)) return 0;
    memcpy(be_u, tu, sizeof(int) * (size_t)m);
    memcpy(be_v, tv, sizeof(int) * (size_t)m);
    best_n = n;
    best_m = m;
    return 1;
}

/* ------------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit min_n\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int minn = atoi(argv[5]);
    int ch;
    while ((ch = getchar()) != EOF) {}
    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    best_n = minn;
    best_m = 0;
    init_factors();

    long hi = moore / 2;
    if (hi > MAXN) hi = MAXN;
    long lo = minn / 2 + 1;
    if (lo < d) lo = d;
    build_candidates(lo, hi);

    double slice = 0.3;
    while (now() < t_end) {
        int progressed = 0;
        for (int c = 0; c < nc && now() < t_end; c++) {
            if (2 * cand[c].N <= best_n) continue;
            Spec sp;
            if (cand[c].j < 0) sp = F[cand[c].i];
            else spec_prod(&sp, &F[cand[c].i], &F[cand[c].j]);
            int N = build_group(&sp, MAXN);
            if (N != cand[c].N || N < d) continue;
            if (!build_tables(N, sp.deg)) continue;
            NG = N;
            progressed = 1;
            double until = now() + slice;
            if (until > t_end) until = t_end;
            if (anneal(until)) store_graph();
        }
        if (!progressed) break;
        slice *= 1.5;
    }

    if (best_m == 0) {
        printf("0 0\n");
    } else {
        printf("%d %d\n", best_n, best_m);
        for (int k = 0; k < best_m; k++) printf("%d %d\n", be_u[k], be_v[k]);
    }
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

    def left():
        return 0.9 * time_limit - 2.0 - (time.monotonic() - t0)

    if left() < 2.0:
        return best

    # Stage 1: the parent's lift engine, half of the usable time.
    lift_budget = 0.5 * left()
    try:
        text = lib.run_c(LIFT_C, [d, D, seed, round(lift_budget, 2)],
                         stdin_graph=best, timeout=lift_budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))

    # Stage 2: Haar graphs over non-metacyclic groups, must beat the current order.
    if d >= 2 and D >= 2 and left() >= 2.0:
        hb = left()
        try:
            text = lib.run_c(HAAR_C, [d, D, seed + 1, round(hb, 2), best[0]],
                             stdin_graph=None, timeout=hb + 5)
            consider(lib.parse_graph_text(text))
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
