"""Combined program: Python builds the best algebraic start (PG(2,q), W(q), Araujo-Pardo-Lopez,
or K_{d,d}) and checks it with lib.is_valid.

New in this version: a group-Haar phase. Haar graphs H(G,S) over finite groups G that are not
necessarily metacyclic (direct and wreath products, affine groups, small permutation groups,
S_n/A_n, GL/SL(2,3)) are searched for diameter D with a hill-climb in C. A valid Haar graph of
order 2|G| larger than the current best replaces the start. Then the C growth engine runs
from whichever start is largest. Every candidate is checked with lib.is_valid, and K_{d,d} is
the fallback."""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Voltage lifts over semidirect groups Z_m x|_r Z_k, base multigraphs on p <= 4 vertices per
 *    side. The diameter objective is orbit-reduced: BFS from the 2p fibre representatives only.
 * 2. Saturation: greedily add missing A-B edges between vertices with spare degree. Adding an
 *    edge never increases a distance, so validity is preserved.
 * 3. Hybrid growth: either insert one vertex pair and anneal (grow), or delete k vertex pairs,
 *    insert k+1 pairs and anneal (regrow / ruin-and-recreate). Both add exactly 2 vertices.
 * 4. Haar mode: usage prog d D seed time_limit haar < table. The table is a group of order m
 *    given as the pairs (x*m+y, x*y), with 0 the identity. It hill-climbs a d-subset S so that
 *    the Haar graph H(G,S) has diameter <= D, and prints it.
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

/* Full all-pairs check by bitsets: number of unordered pairs at distance > D. */
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

/* Saturation: adding an A-B edge between two vertices with spare degree never increases any
 * distance, so a valid graph stays valid. Fills spare slots greedily; returns edges added. */
static int saturate(Graph *g) {
    int added = 0;
    for (int a = 0; a < g->n; a++) {
        if (g->side[a] != 0 || g->deg[a] >= d) continue;
        for (int b = 0; b < g->n && g->deg[a] < d; b++) {
            if (g->side[b] != 1 || g->deg[b] >= d || has_edge(g, a, b)) continue;
            add_edge(g, a, b);
            added++;
        }
    }
    return added;
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

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
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

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x. */
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

/* Orbit-reduced diameter objective for a regular-fibre lift.
 * The group acts by left multiplication on every fibre, so the distance between (a, x) and
 * (b, y) equals the distance between (a, e) and (b, x^-1 y). Hence it is enough to BFS from the
 * 2p representatives b*N (element 0 of each fibre). Returns the number of (representative,
 * vertex) pairs at distance > D, which is zero exactly when the lift has diameter <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p, int N) {
    int nv = g->n;
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

/* Hill-climb the voltages of one random base multigraph over the group G. */
static int lift_fast_try(Graph *g, int p, int N, const Grp *G, int steps, double until) {
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
    long bad = orbit_bad(g, p, N);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, G, dt, nd);
        long nb = orbit_bad(g, p, N);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, G, dt, nd);
    return bad == 0;
}

/* Search lifts of size 2pN strictly larger than the current best. Each accepted lift is
 * saturated before it becomes the new best. */
static void fast_lift_search(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int r = rndint(20);
        int p = r < 8 ? 1 : r < 14 ? 2 : r < 18 ? 3 : 4;
        long target = best->n + 2;
        if (target > moore) return;
        int Nmin = (int)((target + 2 * p - 1) / (2 * p));
        int N = Nmin + rndint(3);
        if (N < d) N = d;
        if (2L * p * N > moore || 2 * p * N > MAXN) continue;
        if (!random_group(N, &G)) continue;
        for (int a = 0; a < 3 && now() < until; a++) {
            if (lift_fast_try(&cand, p, N, &G, 20000, until) && is_valid(&cand) &&
                cand.n > best->n) {
                saturate(&cand);
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* Remove vertex v (and its edges). The last vertex is moved into slot v so the labels stay
 * 0..n-1. Sides are preserved. */
static void remove_vertex(Graph *g, int v) {
    for (int i = 0; i < g->deg[v]; i++) del_half(g, g->adj[v][i], v);
    g->deg[v] = 0;
    int last = g->n - 1;
    if (v != last) {
        for (int i = 0; i < g->deg[last]; i++) {
            int u = g->adj[last][i];
            for (int j = 0; j < g->deg[u]; j++)
                if (g->adj[u][j] == last) { g->adj[u][j] = v; break; }
        }
        g->deg[v] = g->deg[last];
        memcpy(g->adj[v], g->adj[last], sizeof(int) * g->deg[last]);
        g->side[v] = g->side[last];
        g->deg[last] = 0;
    }
    g->n--;
}

/* Append one A-vertex x = n and one B-vertex y = n+1 joined by an edge. Each gets d-1 more
 * edges by stealing existing A-B edges (a,b) -> (x,b) and (y,a), which keeps all old degrees. */
static void attach_pair(Graph *work) {
    int n = work->n;
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
}

/* Simulated annealing on degree-preserving A-B edge swaps until bad_pairs == 0.
 * Returns 1 on success, 0 on timeout. */
static int anneal(Graph *work, double until) {
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
    return 1;
}

/* Growth step: best + one vertex pair, then anneal. */
static int grow_once(const Graph *best, Graph *work, double until) {
    if (best->n + 2 > moore_bound() || best->n + 2 > MAXN) return 0;
    copy_graph(work, best);
    attach_pair(work);
    if (!anneal(work, until)) return 0;
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
}

/* Ruin-and-recreate. Delete k random A/B vertex pairs, then insert k+1 fresh pairs (net
 * +2 vertices), saturate the spare slots, and anneal the diameter back to D. */
static int regrow(const Graph *best, Graph *work, int k, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN || n <= 4 * k + 2) return 0;
    copy_graph(work, best);
    for (int r = 0; r < k; r++) {
        for (int s = 0; s < 2; s++) {
            int v;
            do {
                v = rndint(work->n);
            } while (work->side[v] != s);
            remove_vertex(work, v);
        }
    }
    for (int r = 0; r < k + 1; r++) attach_pair(work);
    saturate(work);
    if (work->n != n + 2) return 0;
    if (!anneal(work, until)) return 0;
    if (!is_valid(work)) return 0;
    saturate(work);
    return 1;
}

/* Alternate growth steps and ruin-and-recreate steps, keeping whichever gives a strictly
 * larger valid graph. */
static void hybrid_search(Graph *best, double until) {
    static Graph work;
    while (now() < until && best->n + 2 <= moore_bound()) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        double until2 = now() + slice;
        int ok;
        if (rndint(2) == 0) {
            ok = grow_once(best, &work, until2);
        } else {
            int k = 1 + rndint(3);
            ok = regrow(best, &work, k, until2);
        }
        if (ok && work.n > best->n) copy_graph(best, &work);
    }
}

/* Haar mode. Group table with m = order, identity 0, gT[x][y] = x*y. */
#define MAXG 512
static int gm;
static int gT[MAXG][MAXG];
static int ginv[MAXG];
static int hdist[2 * MAXG], hq[2 * MAXG];

/* Number of vertices of H(G,S) not within distance D of a_e or b_e (zero iff diameter <= D). */
static int haar_bad(const int *S) {
    int n2 = 2 * gm, total = 0;
    for (int src = 0; src < 2; src++) {
        int s0 = src ? gm : 0;
        for (int v = 0; v < n2; v++) hdist[v] = -1;
        int head = 0, tail = 0;
        hdist[s0] = 0;
        hq[tail++] = s0;
        while (head < tail) {
            int v = hq[head++];
            if (hdist[v] >= D) continue;
            for (int i = 0; i < d; i++) {
                int u = v < gm ? gm + gT[v][S[i]] : gT[v - gm][ginv[S[i]]];
                if (hdist[u] < 0) {
                    hdist[u] = hdist[v] + 1;
                    hq[tail++] = u;
                }
            }
        }
        total += n2 - tail;
    }
    return total;
}

static int haar_main(double limit) {
    long n, cnt;
    double t_stop = now() + limit * 0.9;
    if (scanf("%ld %ld", &n, &cnt) != 2 || n <= 0 || n > (long)MAXG * MAXG || cnt != n) {
        printf("0 0\n");
        return 0;
    }
    int m = 0;
    while ((long)(m + 1) * (m + 1) <= n) m++;
    if ((long)m * m != n || m < d || m > MAXG) {
        printf("0 0\n");
        return 0;
    }
    gm = m;
    for (long e = 0; e < cnt; e++) {
        long u, v;
        if (scanf("%ld %ld", &u, &v) != 2 || u < 0 || u >= n || v < 0 || v >= m) {
            printf("0 0\n");
            return 0;
        }
        gT[u / m][u % m] = (int)v;
    }
    for (int x = 0; x < m; x++) {
        ginv[x] = -1;
        for (int y = 0; y < m; y++)
            if (gT[x][y] == 0) { ginv[x] = y; break; }
        if (ginv[x] < 0) {
            printf("0 0\n");
            return 0;
        }
    }
    static int S[MAXD];
    while (now() < t_stop) {
        for (int i = 0; i < d; i++) {
            int c, ok;
            do {
                c = rndint(m);
                ok = 1;
                for (int j = 0; j < i; j++)
                    if (S[j] == c) ok = 0;
            } while (!ok);
            S[i] = c;
        }
        int bad = haar_bad(S);
        for (int s = 0; s < 4000 && bad > 0; s++) {
            if ((s & 63) == 0 && now() > t_stop) break;
            int i = rndint(d), c = rndint(m), dup = 0;
            for (int j = 0; j < d; j++)
                if (S[j] == c) dup = 1;
            if (dup) continue;
            int old = S[i];
            S[i] = c;
            int nb = haar_bad(S);
            if (nb <= bad || rnd01() < 0.02) bad = nb;
            else S[i] = old;
        }
        if (bad == 0) {
            printf("%d %d\n", 2 * m, m * d);
            for (int g = 0; g < m; g++)
                for (int i = 0; i < d; i++)
                    printf("%d %d\n", g, m + gT[g][S[i]]);
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [haar] < start_graph\n", argv[0]);
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

    if (argc >= 6 && strcmp(argv[5], "haar") == 0) {
        if (d < 1 || d > MAXD || D < 1) {
            printf("0 0\n");
            return 0;
        }
        return haar_main(limit);
    }

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (best.n > 0) {
        saturate(&best);
        if (!is_valid(&best)) read_start(&best);
    }

    if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
        fast_lift_search(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) hybrid_search(&best, t_end);
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


# ---------------------------------------------------------------- finite groups
# A group is (m, T): elements 0..m-1, identity 0, T[x][y] = index of x*y.

def _pmul(x, y):
    """Composition of permutations given as tuples."""
    return tuple(x[i] for i in y)


def _closure_table(gens, ident, mul, lo, hi):
    """Group generated by gens (right multiplication from identity), if its order is in [lo, hi]."""
    cap = hi + 1
    elems = [ident]
    index = {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = mul(x, g)
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
    m = len(elems)
    if m < lo or m > hi:
        return None
    return m, [[index[mul(a, b)] for b in elems] for a in elems]


def _perm_group(gens, lo, hi):
    return _closure_table(gens, tuple(range(len(gens[0]))), _pmul, lo, hi)


def _mat_mul(p):
    def mul(X, Y):
        a, b, c, d = X
        e, f, g, h = Y
        return ((a * e + b * g) % p, (a * f + b * h) % p,
                (c * e + d * g) % p, (c * f + d * h) % p)
    return mul


def _matrix_group(p, gens, lo, hi):
    return _closure_table(gens, (1, 0, 0, 1), _mat_mul(p), lo, hi)


def _wreath_gens(a, b):
    """Generators of Z_a wr Z_b acting on a*b points (block i, coordinate j -> i*a + j)."""
    t = a * b
    cyc = [0] * t
    base = list(range(t))
    for i in range(b):
        for j in range(a):
            cyc[i * a + j] = ((i + 1) % b) * a + j
    for j in range(a):
        base[j] = (j + 1) % a
    return [tuple(cyc), tuple(base)]


def _affine_perm(p, lin, tx, ty):
    """Affine map x -> lin * x + (tx, ty) on F_p^2, as a permutation of p*p points."""
    a, b, c, d = lin
    perm = [0] * (p * p)
    for x in range(p):
        for y in range(p):
            X = (a * x + b * y + tx) % p
            Y = (c * x + d * y + ty) % p
            perm[x * p + y] = X * p + Y
    return tuple(perm)


def _cyclic(m):
    return m, [[(x + y) % m for y in range(m)] for x in range(m)]


def _direct(G, H):
    mG, TG = G
    mH, TH = H
    m = mG * mH
    T = [[0] * m for _ in range(m)]
    for x in range(mG):
        for y in range(mH):
            row = T[x * mH + y]
            tyrow = TH[y]
            for x2 in range(mG):
                a = TG[x][x2] * mH
                base = x2 * mH
                for y2 in range(mH):
                    row[base + y2] = a + tyrow[y2]
    return m, T


def _semidirect(m, k, r):
    order, mul, _ = lib.semidirect_group(m, k, r)
    return order, [[mul(x, y) for y in range(order)] for x in range(order)]


def _base_groups(hi):
    """Small non-cyclic groups used as factors (orders at most hi)."""
    out = []

    def keep(G):
        if G is not None and G[0] <= hi:
            out.append(G)

    keep(_perm_group([(1, 0, 2), (1, 2, 0)], 1, hi))                    # S3
    keep(_perm_group([(1, 2, 0, 3), (1, 0, 3, 2)], 1, hi))              # A4
    keep(_perm_group([(1, 0, 2, 3), (1, 2, 3, 0)], 1, hi))              # S4
    keep(_perm_group([(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)], 1, hi))        # A5
    keep(_perm_group([(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)], 1, hi))        # S5
    for n in range(3, hi // 2 + 1):                                     # dihedral, order 2n
        rot = tuple((i + 1) % n for i in range(n))
        ref = tuple((-i) % n for i in range(n))
        keep(_perm_group([rot, ref], 1, hi))
    keep(_matrix_group(3, [(1, 1, 0, 1), (0, 2, 1, 0)], 1, hi))         # SL(2,3)
    keep(_matrix_group(3, [(1, 1, 0, 1), (0, 2, 1, 0), (1, 0, 0, 2)], 1, hi))  # GL(2,3)
    for a, b in [(2, 2), (2, 3), (2, 4), (3, 2), (3, 3), (4, 2), (5, 2)]:
        if a ** b * b <= hi:
            keep(_perm_group(_wreath_gens(a, b), 1, hi))
    return out


def _catalogue(lo, hi, rng, per_order):
    """Groups of each order in [lo, hi], at most per_order per order."""
    buckets = {M: [] for M in range(lo, hi + 1)}

    def open_(M):
        return lo <= M <= hi and len(buckets[M]) < per_order

    def offer(make, M=None):
        if M is not None and not open_(M):
            return
        try:
            G = make()
        except Exception:
            return
        if G is not None and open_(G[0]):
            buckets[G[0]].append(G)

    for M in range(lo, hi + 1):
        offer(lambda M=M: _cyclic(M), M)
    for a in range(2, hi + 1):
        for b in range(a, hi // a + 1):
            offer(lambda a=a, b=b: _direct(_cyclic(a), _cyclic(b)), a * b)
    for M in range(lo, hi + 1):
        for k in range(2, M):
            if M % k or not open_(M):
                continue
            m = M // k
            if m < 2:
                continue
            rs = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
            rng.shuffle(rs)
            for r in rs[:3]:
                offer(lambda m=m, k=k, r=r: _semidirect(m, k, r), M)
    base = _base_groups(hi)
    for H in base:
        for k in range(2, hi + 1):
            if H[0] * k > hi:
                break
            offer(lambda H=H, k=k: _direct(H, _cyclic(k)), H[0] * k)
    for i, H in enumerate(base):
        for K in base[i:]:
            offer(lambda H=H, K=K: _direct(H, K), H[0] * K[0])
    for p in (3, 5, 7):
        mats = [(a, b, c, e) for a, b, c, e in itertools.product(range(p), repeat=4)
                if (a * e - b * c) % p]
        rng.shuffle(mats)
        for A in mats[:40]:
            gens = [_affine_perm(p, (1, 0, 0, 1), 1, 0),
                    _affine_perm(p, (1, 0, 0, 1), 0, 1),
                    _affine_perm(p, A, 0, 0)]
            offer(lambda gens=gens, p=p: _closure_table(
                gens, tuple(range(p * p)), _pmul, lo, hi))
    for _ in range(150):
        t = rng.randint(6, 9)
        gens = []
        for _ in range(2):
            pm = list(range(t))
            rng.shuffle(pm)
            gens.append(tuple(pm))
        offer(lambda gens=gens, t=t: _closure_table(
            gens, tuple(range(t)), _pmul, lo, hi))
    return buckets


def _haar_phase(d, D, lo, hi, rng, until):
    """Search Haar graphs H(G,S) over groups of order M in [lo, hi], ascending in M.
    Returns the largest valid graph found, or None."""
    buckets = _catalogue(lo, hi, rng, 10)
    best = None
    try:
        for M in range(lo, hi + 1):
            now = time.monotonic()
            if now >= until:
                break
            groups = buckets[M]
            if not groups or M < d:
                continue
            slice_end = now + max(0.5, (until - now) / (hi - M + 1))
            found = None
            k = 0
            while found is None and time.monotonic() < slice_end - 0.2:
                m, T = groups[k % len(groups)]
                k += 1
                budget = min(1.5, slice_end - time.monotonic())
                pairs = [(x * m + y, T[x][y]) for x in range(m) for y in range(m)]
                text = lib.run_c(C_SOURCE, [d, D, rng.randrange(1 << 30), budget, "haar"],
                                 stdin_graph=(m * m, pairs), timeout=budget + 5)
                n, edges = lib.parse_graph_text(text)
                if n > 0 and lib.is_valid(n, edges, d, D):
                    found = (n, edges)
            if found is not None:
                best = found
    except Exception:
        pass
    return best


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

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    # Phase 1: Haar graphs over non-metacyclic groups, in orders above the current best
    # (and not far below the Moore-based target range).
    rng = random.Random(seed * 1000003 + d * 911 + D)
    if D >= 3:
        lo = max(best[0] // 2 + 1, moore // 3 + 1)
        hi = min(lo + 12, moore // 2)
        if lo <= hi:
            try:
                found = _haar_phase(d, D, lo, hi, rng, t0 + 0.22 * time_limit)
                if found is not None and found[0] > best[0] and lib.is_valid(found[0], found[1], d, D):
                    best = found
            except Exception:
                pass

    # Phase 2: C growth engine from the best start so far.
    budget = 0.88 * time_limit - (time.monotonic() - t0) - 1.5
    if budget > 0.2:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                             stdin_graph=best, timeout=budget + 5)
            out = lib.parse_graph_text(text)
            if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
                best = out
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
