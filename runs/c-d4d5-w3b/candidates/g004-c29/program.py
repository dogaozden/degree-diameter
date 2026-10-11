"""Bi-Cayley lift search over a wide family of finite groups, then ruin-and-regrow growth.

Changes from the parent:
- Group families are generated inside C, not supplied from Python: cyclic, Z_a x Z_b (a | b),
  dihedral D_n, dicyclic Dic_n, D_n x Z_c, and metacyclic Z_m x|_r Z_k. The parent used only
  metacyclic groups.
- The lift search stratifies by fibre count p in 1..4 and group order N in [ceil(target/2p),
  +3], so it keeps working as the best graph grows. The parent fixed N once.
- Lifts use a group-generic orbit-reduced diameter test: BFS from the 2p fibre representatives,
  using left multiplication (valid for any group with identity at element 0).
- Growth is unchanged: grow-by-two and ruin-and-regrow with degree-preserving swap annealing.

Every output is validated in C and again in Python. Python falls back to the best algebraic
start, or K_{d,d}, if the engine fails."""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Bi-Cayley lifts: a random d-regular base multigraph on p+p vertices, voltages in a
 *    finite group G of order N. Groups come from an in-C family (cyclic, Z_a x Z_b,
 *    dihedral, dicyclic, D_n x Z_c, metacyclic). Diameter is checked on the 2p fibre
 *    representatives only (left-multiplication symmetry).
 * 2. Grow by two and ruin-and-regrow with degree-preserving swap annealing.
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
#define MAXDESC 512

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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D.
 * Also fills badv[v] = number of vertices at distance > D from v. */
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

/* ---------------------------------------------------------------- groups
 * Identity is element 0 in every family.
 *   type 0: Z_N                       (N)
 *   type 1: Z_a x Z_b, a | b          (p1=a, p2=b)     element a1*b + b1
 *   type 2: dihedral D_n, order 2n    (p1=n)           element e*n + a  (r^a s^e)
 *   type 3: dicyclic Dic_n, order 4n  (p1=n)           element e*2n + a (x^a y^e)
 *   type 4: D_n x Z_c, order 2n*c     (p1=n, p2=c)     element dih*c + z
 *   type 5: Z_m x|_r Z_k              (p1=m, p2=k, p3=r) element a*k + b
 */
typedef struct { int type, N, p1, p2, p3; } GDesc;
static GDesc descs[MAXDESC];
static int ndesc;
static GDesc CG;
static int RPW[MAXN];

static void add_desc(int type, int N, int p1, int p2, int p3) {
    if (ndesc >= MAXDESC) return;
    GDesc *g = &descs[ndesc++];
    g->type = type; g->N = N; g->p1 = p1; g->p2 = p2; g->p3 = p3;
}

static void enum_groups(int N) {
    ndesc = 0;
    add_desc(0, N, N, 0, 0);
    for (int a = 2; a * a <= N; a++)
        if (N % (a * a) == 0) add_desc(1, N, a, N / a, 0);
    if (N % 2 == 0 && N / 2 >= 2) add_desc(2, N, N / 2, 0, 0);
    if (N % 4 == 0 && N / 4 >= 2) add_desc(3, N, N / 4, 0, 0);
    for (int c = 2; 4 * c <= N; c++)
        if (N % (2 * c) == 0 && N / (2 * c) >= 2) add_desc(4, N, N / (2 * c), c, 0);
    for (int m = 3; m <= N / 2; m++) {
        if (N % m) continue;
        int k = N / m;
        if (k < 2) continue;
        int cnt = 0;
        for (int r = 2; r < m && cnt < 4; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            add_desc(5, N, m, k, r);
            cnt++;
        }
    }
}

static void set_group(const GDesc *g) {
    CG = *g;
    if (g->type == 5) {
        int m = g->p1, k = g->p2;
        RPW[0] = 1 % m;
        for (int b = 1; b < k; b++) RPW[b] = (int)((long)RPW[b - 1] * g->p3 % m);
    }
}

static int gmul(int x, int y) {
    switch (CG.type) {
    case 0:
        return (x + y) % CG.N;
    case 1: {
        int b = CG.p2, a = CG.p1;
        int x1 = x / b, x2 = x % b, y1 = y / b, y2 = y % b;
        return ((x1 + y1) % a) * b + (x2 + y2) % b;
    }
    case 2: {
        int n = CG.p1, e = x / n, a = x % n, f = y / n, c = y % n;
        int ca = e ? (n - c) % n : c;
        return ((e + f) & 1) * n + (a + ca) % n;
    }
    case 3: {
        int n = CG.p1, M = 2 * n;
        int e = x / M, a = x % M, f = y / M, c = y % M;
        int ca = e ? (M - c) % M : c;
        int na = (a + ca) % M, ne = e + f;
        if (ne == 2) { ne = 0; na = (na + n) % M; }
        return ne * M + na;
    }
    case 4: {
        int n = CG.p1, c = CG.p2;
        int u = x / c, z = x % c, v = y / c, w = y % c;
        int e = u / n, a = u % n, f = v / n, cc = v % n;
        int ca = e ? (n - cc) % n : cc;
        int dih = ((e + f) & 1) * n + (a + ca) % n;
        return dih * c + (z + w) % c;
    }
    case 5: {
        int m = CG.p1, k = CG.p2;
        int a = x / k, b = x % k, c = y / k, e = y % k;
        return (int)(((long)a + (long)RPW[b] * c) % m) * k + (b + e) % k;
    }
    }
    return 0;
}

/* ---------------------------------------------------------------- lifts */
typedef struct { int i, j, g; } Dart;

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

/* Layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = CG.N;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static int dist_buf[MAXN], queue_buf[MAXN];

/* Orbit-reduced count of (representative, vertex) pairs at distance > D. Zero iff the lift
 * has diameter <= D. Representatives are element 0 of each fibre (the identity). */
static long orbit_bad(const Graph *g, int p) {
    int nv = g->n;
    int N = CG.N;
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

/* Hill-climb the voltages of one random base multigraph over the current group. */
static int lift_fast_try(Graph *g, int p, int steps, double until) {
    int N = CG.N;
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            if (M[i][j] > N) return 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i; dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, dt, nd);
    long bad = orbit_bad(g, p);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, dt, nd);
    return bad == 0;
}

/* Search lifts of order 2pN, with N in [ceil(target/2p), +3] for a random fibre count p.
 * The window moves with the current best, so the search keeps going as the graph grows. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long target = best->n + 2;
        if (target > moore) return;
        int p = 1 + rndint(4);
        long Nmin = (target + 2L * p - 1) / (2L * p);
        long Nl = Nmin + rndint(4);
        if (Nl < 2 || 2L * p * Nl > moore || 2L * p * Nl > MAXN) continue;
        int N = (int)Nl;
        enum_groups(N);
        if (ndesc == 0) continue;
        set_group(&descs[rndint(ndesc)]);
        if (lift_fast_try(&cand, p, 20000, until) && is_valid(&cand) && cand.n > best->n)
            copy_graph(best, &cand);
    }
}

/* ---------------------------------------------------------------- growth */

/* Bad-pair roulette: a uniformly random vertex in some bad pair (from the latest badv[]). */
static int pick_bad_vertex(const Graph *g) {
    static int list[MAXN];
    int c = 0;
    for (int v = 0; v < g->n; v++)
        if (badv[v] > 0) list[c++] = v;
    if (c == 0) return -1;
    return list[rndint(c)];
}

/* Degree-preserving swap annealing. Returns 1 iff the graph becomes valid before the deadline. */
static int anneal(Graph *work, double until) {
    long bad = bad_pairs(work);
    double T = 1.0;
    long it = 0;
    while (bad > 0) {
        if ((++it & 15) == 0 && now() > until) return 0;
        int v;
        if (rnd01() < 0.8) {
            v = pick_bad_vertex(work);
            if (v < 0) v = rndint(work->n);
        } else {
            v = rndint(work->n);
        }
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
            bad_pairs(work);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    return is_valid(work);
}

/* Grow by two: one new vertex per side, joined to each other, with d-1 stolen edges each. */
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
    return anneal(work, until);
}

/* Ruin and regrow: delete a BFS ball (K0 side-0, K1 side-1 vertices), add K0+1 side-0 and
 * K1+1 side-1 vertices, match the stub deficits randomly without multi-edges, then anneal. */
static int ruin_regrow(const Graph *cur, Graph *out, double until) {
    int n = cur->n;
    if (n < 4 || n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static int rem[MAXN], map[MAXN], seen[MAXN], q[MAXN];
    int K0 = 1 + rndint(3), K1 = 1 + rndint(3);
    memset(rem, 0, sizeof(int) * n);
    memset(seen, 0, sizeof(int) * n);
    int root = rndint(n);
    int head = 0, tail = 0, c0 = 0, c1 = 0;
    q[tail++] = root;
    seen[root] = 1;
    while (head < tail && (c0 < K0 || c1 < K1)) {
        int v = q[head++];
        if (cur->side[v] == 0 && c0 < K0) { rem[v] = 1; c0++; }
        else if (cur->side[v] == 1 && c1 < K1) { rem[v] = 1; c1++; }
        for (int i = 0; i < cur->deg[v]; i++) {
            int u = cur->adj[v][i];
            if (!seen[u]) { seen[u] = 1; q[tail++] = u; }
        }
    }
    if (c0 < K0 || c1 < K1) return 0;

    int N = 0;
    for (int v = 0; v < n; v++)
        if (!rem[v]) map[v] = N++;
    int total = N + (K0 + 1) + (K1 + 1);
    if (total != n + 2 || total > MAXN) return 0;
    out->n = total;
    for (int v = 0; v < total; v++) { out->deg[v] = 0; out->side[v] = 0; }
    for (int v = 0; v < n; v++)
        if (!rem[v]) out->side[map[v]] = cur->side[v];
    int id = N;
    for (int k = 0; k < K0 + 1; k++) out->side[id++] = 0;
    for (int k = 0; k < K1 + 1; k++) out->side[id++] = 1;

    for (int v = 0; v < n; v++) {
        if (rem[v]) continue;
        for (int i = 0; i < cur->deg[v]; i++) {
            int u = cur->adj[v][i];
            if (rem[u] || u < v) continue;
            add_edge(out, map[v], map[u]);
        }
    }

    long s0 = 0, s1 = 0;
    for (int v = 0; v < total; v++) {
        int def = d - out->deg[v];
        if (def < 0) return 0;
        if (out->side[v] == 0) s0 += def;
        else s1 += def;
    }
    if (s0 != s1) return 0;

    long need = s0;
    long guard = 0;
    while (need > 0) {
        if (++guard > 2000000L) return 0;
        int a = rndint(total);
        if (out->side[a] != 0 || out->deg[a] >= d) continue;
        int b = rndint(total);
        if (out->side[b] != 1 || out->deg[b] >= d) continue;
        if (has_edge(out, a, b)) continue;
        add_edge(out, a, b);
        need--;
    }
    return anneal(out, until);
}

/* Alternate grow-by-two and ruin-and-regrow from the frontier. The frontier moves only on
 * success, so the size never decreases. */
static void grow_search(Graph *best, double until) {
    static Graph cur, work;
    copy_graph(&cur, best);
    while (now() < until && cur.n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        int first_ruin = rnd01() < 0.5;
        int ok = 0;
        for (int a = 0; a < 2 && !ok && now() < until; a++) {
            int use_ruin = (a == 0) ? first_ruin : !first_ruin;
            double dl = now() + slice;
            if (dl > until) dl = until;
            if (use_ruin) ok = ruin_regrow(&cur, &work, dl);
            else ok = grow_once(&cur, &work, dl);
        }
        if (ok) {
            copy_graph(&cur, &work);
            if (cur.n > best->n) copy_graph(best, &cur);
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
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
        fast_lift_search(&best, t0 + (t_end - t0) * 0.5);
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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 4)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
