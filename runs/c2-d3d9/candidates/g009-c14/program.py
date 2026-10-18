"""Combined bi-Cayley / lift / grow search engine.

Stage 1 (bi-Cayley): vertices A_x, B_y with x, y in a metacyclic group G = Z_m x| Z_k of
order N, and edges A_x ~ B_{x s} for s in S (|S| = d, identity in S). Left multiplication
is an automorphism that is transitive on each side, so two BFS runs decide the diameter.
Groups are sampled nonabelian first. Orders N are scanned downward from the Moore limit.
After each success the scan restarts with a higher lower bound, so it keeps pushing up.

Stage 2 (voltage lifts): if no bi-Cayley improvement is found, hill-climb voltages on
small random base graphs over the same groups.

Stage 3 (grow by two): insert one vertex per side and anneal edge swaps until diameter <= D.

Every accepted graph is checked with an exact bitset diameter test. Python keeps the best
valid graph (known start, trivial fallback, or C output) and checks it with lib.is_valid.
"""
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

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define CAY_MAX 1100
#define MAXGRP 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

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
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * (size_t)src->deg[v]);
    }
}

/* ------------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN]; /* badv[v] = vertices farther than D from v, after bad_pairs() */

/* Number of unordered pairs at distance > D (0 means connected with diameter <= D). */
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

/* Full validity check: simple, bipartite (by side labels), degree <= d, diameter <= D. */
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

/* Read "n m" + edges from stdin and 2-colour it. Leaves g->n = 0 if absent or invalid. */
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

/* Z_m x|_r Z_k: element (a, b) is the int a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
typedef struct {
    int m, k, r;
    int rp[MAXN]; /* rp[b] = r^b mod m */
} Grp;

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniform random (m, k, r) with m*k = N, gcd(r, m) = 1, r^k = 1 mod m. */
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

/* Group descriptors for a fixed order N; nonabelian ones (r != 1) are listed first. */
typedef struct { int m, k, r; } GDesc;
static GDesc gl[MAXGRP];
static int gl_count, gl_nonab;

static void list_groups(int N) {
    gl_count = 0;
    gl_nonab = 0;
    for (int pass = 0; pass < 2; pass++) {
        for (int m = 1; m <= N; m++) {
            if (N % m) continue;
            int k = N / m;
            if (m == 1) {
                if (pass == 1 && gl_count < MAXGRP) {
                    gl[gl_count].m = 1; gl[gl_count].k = k; gl[gl_count].r = 0;
                    gl_count++;
                }
                continue;
            }
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1) continue;
                int nonab = (r != 1);
                if ((pass == 0) != nonab) continue;
                if (gl_count < MAXGRP) {
                    gl[gl_count].m = m; gl[gl_count].k = k; gl[gl_count].r = r;
                    gl_count++;
                }
            }
        }
        if (pass == 0) gl_nonab = gl_count;
    }
}

/* ------------------------------------------------------------------ bi-Cayley graphs */

static int *cmul = NULL; /* cmul[x*N + y] = x*y in the current group of order cN */
static int *cinv = NULL; /* inverses */
static int cN = 0;
static int cS[MAXD], cSinv[MAXD];
static int cdist[2 * CAY_MAX], cq[2 * CAY_MAX];
static Graph cand_g;

static int build_group(int m, int k, int r) {
    int N = m * k;
    int *rp = malloc(sizeof(int) * (size_t)k);
    int *nm = realloc(cmul, sizeof(int) * (size_t)N * (size_t)N);
    if (!rp || !nm) { free(rp); return 0; }
    cmul = nm;
    int *ni = realloc(cinv, sizeof(int) * (size_t)N);
    if (!ni) { free(rp); return 0; }
    cinv = ni;
    for (int b = 0; b < k; b++) rp[b] = (int)powmod(r, b, m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            cmul[x * N + y] = (int)((a + (long)rp[b] * c) % m) * k + (b + e) % k;
        }
    }
    for (int x = 0; x < N; x++) {
        cinv[x] = 0;
        for (int y = 0; y < N; y++)
            if (cmul[x * N + y] == 0) { cinv[x] = y; break; }
    }
    cN = N;
    free(rp);
    return 1;
}

/* Random connection set S = {e, s_1, ..., s_{d-1}} (identity WLOG). Returns 0 on failure. */
static int random_set(int N) {
    cS[0] = 0;
    int c = 1;
    for (int tries = 0; c < d; tries++) {
        if (tries > 100000) return 0;
        int x = 1 + rndint(N - 1), dup = 0;
        for (int i = 0; i < c; i++)
            if (cS[i] == x) { dup = 1; break; }
        if (!dup) cS[c++] = x;
    }
    for (int i = 0; i < d; i++) cSinv[i] = cinv[cS[i]];
    return 1;
}

/* Diameter test: left multiplication is transitive on each side, so BFS from A_e and B_e
 * decides the diameter of the whole bi-Cayley graph. */
static int cayley_ok(int N) {
    int V = 2 * N;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? N : 0;
        for (int v = 0; v < V; v++) cdist[v] = -1;
        int head = 0, tail = 0;
        cdist[s0] = 0;
        cq[tail++] = s0;
        while (head < tail) {
            int v = cq[head++];
            if (cdist[v] >= D) continue;
            if (v < N) {
                for (int i = 0; i < d; i++) {
                    int u = N + cmul[v * N + cS[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            } else {
                int y = v - N;
                for (int i = 0; i < d; i++) {
                    int u = cmul[y * N + cSinv[i]];
                    if (cdist[u] < 0) { cdist[u] = cdist[v] + 1; cq[tail++] = u; }
                }
            }
        }
        if (tail != V) return 0;
    }
    return 1;
}

/* Scan N downward from the Moore limit. After each success, raise the lower bound and
 * restart the scan. When a full pass finds nothing, sample again until time runs out. */
static void cayley_phase(Graph *best, double until) {
    int Nmax = (int)(moore_bound() / 2);
    if (Nmax > CAY_MAX) Nmax = CAY_MAX;
    for (;;) {
        if (now() >= until) return;
        int Nmin = best->n / 2 + 1;
        if (Nmin < d) Nmin = d;
        if (Nmin < 2) Nmin = 2;
        if (Nmin > Nmax) return;
        int improved = 0;
        for (int N = Nmax; N >= Nmin && !improved; N--) {
            if (now() >= until) return;
            list_groups(N);
            if (gl_count == 0) continue;
            int found = 0;
            for (int batch = 0; batch < 12 && !found; batch++) {
                if (now() >= until) return;
                int gi;
                if (gl_nonab > 0 && (gl_count == gl_nonab || rnd01() < 0.8))
                    gi = rndint(gl_nonab);
                else
                    gi = gl_nonab + rndint(gl_count - gl_nonab);
                if (!build_group(gl[gi].m, gl[gi].k, gl[gi].r)) return;
                for (int t = 0; t < 150 && !found; t++)
                    if (random_set(N) && cayley_ok(N)) found = 1;
            }
            if (found) {
                cand_g.n = 2 * N;
                for (int v = 0; v < cand_g.n; v++) { cand_g.deg[v] = 0; cand_g.side[v] = v >= N; }
                for (int x = 0; x < N; x++)
                    for (int i = 0; i < d; i++) add_edge(&cand_g, x, N + cmul[x * N + cS[i]]);
                if (is_valid(&cand_g) && cand_g.n > best->n) {
                    copy_graph(best, &cand_g);
                    improved = 1;
                }
            }
        }
    }
}

/* ------------------------------------------------------------------ voltage lifts */

typedef struct { int i, j, g; } Dart; /* base A-vertex i -> base B-vertex j, voltage g */

/* Random d-regular bipartite base multigraph with p vertices per side. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (int attempt = 0; attempt < 1000; attempt++) {
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

static void build_lift(Graph *g, int p, int N, const Grp *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(G, x, dt[t].g));
}

/* A voltage not used by other darts between the same base pair; -1 if none in 1000 tries. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (int tries = 0; tries < 1000; tries++) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
    return -1;
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
                int v = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                if (v < 0) return 0;
                dt[nd].g = v;
                nd++;
            }
    if (nd == 0) return 0;
    build_lift(g, p, N, G, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        int nv = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        if (nv < 0) continue;
        dt[t].g = nv;
        build_lift(g, p, N, G, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    if (bad != 0) return 0;
    build_lift(g, p, N, G, dt, nd); /* make sure g holds the accepted voltages */
    return 1;
}

static void lift_search(Graph *best, double until) {
    if (d < 2) return;
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

/* ------------------------------------------------------------------ grow by two */

/* Insert one vertex per side into a copy of best, then anneal edge swaps until valid. */
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
    double t0 = now();
    double span = limit * 0.92;
    t_end = t0 + span;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore_bound()) {
        long before = best.n;
        cayley_phase(&best, t0 + span * 0.8);
        if (best.n == before) lift_search(&best, t0 + span * 0.9);
        if (best.n + 2 <= moore_bound()) grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def trivial_graph(d, D):
    """A small graph that is always valid for the given parameters."""
    if D >= 2 and d >= 2:
        return lib.haar_graph(d, range(d))             # K_{d,d}
    return (2, [(0, 1)])                               # single edge


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = None
    start = known_start(d, D)
    if start is not None and lib.is_valid(start[0], start[1], d, D):
        best = start
    if best is None:
        cand = trivial_graph(d, D)
        best = cand if lib.is_valid(cand[0], cand[1], d, D) else (2, [(0, 1)])

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass   # keep the valid fallback
    return best
