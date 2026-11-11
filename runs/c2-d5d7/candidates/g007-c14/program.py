"""Combined program, greedy-endpoint insertion with ruin-and-recreate repair.

For D >= 6 and d in {3, 5} the start is the incidence graph of the split Cayley hexagon H(q), q = d-1
in {2, 4}: bipartite, degree d, diameter 6, so valid for D = 7. The C grow phase inserts one vertex pair
per step. A greedy routine (wire_greedy) wires the pair one swap at a time, scoring each candidate by
the vertices left unreached from the four endpoints. Then degree-preserving swaps anneal the graph.

NEW: the time budget is less conservative. The C engine now stops at 0.95 of its own limit (was 0.92),
and build() gives it 0.92 of time_limit minus a 1.5 s reserve (was 0.85 minus 1.0). The subprocess
timeout keeps a 3 s margin. This gives the grow phase about 10% more search time per case.

Sampled-source annealing: the swap loop minimises F = sum over a source set S of the number of vertices
unreached within D (one BFS per source). S starts as random vertices and grows with vertices that still
have bad pairs. Whenever F reaches 0, the exact bitset check runs. Ruin-and-recreate bursts and the
final answer use the exact count, so output validity is unchanged. Degrees stay exact, so the graph
stays bipartite and of degree d.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * 1. Voltage lifts over semidirect groups Z_m x|_r Z_k, base multigraphs on p <= 4 vertices per
 *    side. The diameter objective is orbit-reduced: BFS from the 2p fibre representatives only.
 *    Run only when the start graph is small.
 * 2. Grow by two: insert one vertex per side. Greedy endpoint-coverage wiring picks the starting
 *    state with the fewest bad pairs. Degree-preserving edge swaps anneal a sampled-source proxy
 *    objective, with exact checks when the proxy reaches zero. When annealing stalls,
 *    ruin-and-recreate moves cut out a local ball, rematch the freed stubs, and keep the result if
 *    the bad-pair count does not grow.
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
#define INIT_TRIALS 4
#define GREEDY_CAND 24
#define STALL_LIMIT 600
#define RR_BURST 16
#define RR_MAXK 6
#define SRC_INIT 48
#define SRC_ADD 16

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
 * Also sets badv[v] = number of vertices at distance > D from v. */
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
 * The group acts by left multiplication on every fibre, so it is enough to BFS from the 2p
 * representatives b*N. Returns the number of (representative, vertex) pairs at distance > D. */
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

/* Search lifts of size 2pN strictly larger than the current best. */
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
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* Random wiring of one new vertex pair x (side 0), y (side 1) onto best (fallback). */
static void wire_pair(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
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

/* Bounded BFS scratch: bq_mark holds stamps so no array clearing is needed. */
static int bq_dist[MAXN], bq_queue[MAXN], bq_mark[MAXN];
static int bq_stamp = 0;

/* Number of vertices within distance D of src (src included). */
static int ball_size(const Graph *g, int src) {
    int head = 0, tail = 0;
    bq_stamp++;
    bq_mark[src] = bq_stamp;
    bq_dist[src] = 0;
    bq_queue[tail++] = src;
    while (head < tail) {
        int v = bq_queue[head++];
        if (bq_dist[v] >= D) continue;
        for (int i = 0; i < g->deg[v]; i++) {
            int u = g->adj[v][i];
            if (bq_mark[u] != bq_stamp) {
                bq_mark[u] = bq_stamp;
                bq_dist[u] = bq_dist[v] + 1;
                bq_queue[tail++] = u;
            }
        }
    }
    return tail;
}

/* Greedy endpoint-coverage wiring of the new pair x (side 0), y (side 1).
 * Start with x-y. Then d-1 times: sample GREEDY_CAND legal swaps (a on side 0, b on side 1, both
 * old and unused). Each swap removes a-b and adds x-b, y-a. Score the swap by the number of
 * vertices left unreached within distance D from the four endpoints x, y, a, b. Keep the best.
 * Degrees are preserved. Returns 0 if no legal swap is found. */
static int wire_greedy(const Graph *best, Graph *work) {
    static int used[MAXN];
    static int stamp = 0;
    int n = best->n;
    copy_graph(work, best);
    int x = n, y = n + 1;
    work->n = n + 2;
    work->deg[x] = work->deg[y] = 0;
    work->side[x] = 0;
    work->side[y] = 1;
    add_edge(work, x, y);
    stamp++;
    used[x] = used[y] = stamp;
    for (int k = 0; k < d - 1; k++) {
        int ba = -1, bb = -1;
        long bscore = -1;
        int got = 0;
        for (int att = 0; got < GREEDY_CAND && att < 4000; att++) {
            int a = rndint(n);
            if (work->side[a] != 0 || used[a] == stamp || work->deg[a] == 0) continue;
            int b = work->adj[a][rndint(work->deg[a])];
            if (b >= n || used[b] == stamp) continue;
            got++;
            del_edge(work, a, b);
            add_edge(work, x, b);
            add_edge(work, y, a);
            long score = (long)(work->n - ball_size(work, x)) +
                         (long)(work->n - ball_size(work, y)) +
                         (long)(work->n - ball_size(work, a)) +
                         (long)(work->n - ball_size(work, b));
            del_edge(work, x, b);
            del_edge(work, y, a);
            add_edge(work, a, b);
            if (bscore < 0 || score < bscore) { bscore = score; ba = a; bb = b; }
        }
        if (ba < 0) return 0;
        del_edge(work, ba, bb);
        add_edge(work, x, bb);
        add_edge(work, y, ba);
        used[ba] = used[bb] = stamp;
    }
    return 1;
}

/* Ruin-and-recreate move (large-neighbourhood repair).
 * 1. Pick a vertex c that lies on a bad pair, and BFS from it. Collect up to k vertices of side 0
 *    and k of side 1 (a local ball).
 * 2. Delete every edge incident to the collected vertices. Their neighbours now have free stubs.
 * 3. Rematch the stubs at random: each side-0 stub gets a side-1 stub it is not yet adjacent to.
 *    Degrees are exact again, so the graph stays bipartite with max degree d.
 * 4. Keep the move if the bad-pair count does not grow, otherwise accept with a small Metropolis
 *    probability, else restore the saved copy.
 * Returns 1 if the move was accepted. *bad holds the exact bad-pair count of the current graph. */
static Graph ruin_save;
static int rr_chosen[MAXN];
static int rr_astub[MAXN * MAXD], rr_bstub[MAXN * MAXD];
static int rr_bused[MAXN * MAXD];

static int ruin_recreate_step(Graph *work, long *bad, int k) {
    static int mark[MAXN];
    static int rq[MAXN];
    static int stamp = 0;
    int n = work->n;
    if (n <= 0) return 0;
    int c = rndint(n);
    for (int tries = 0; tries < 50 && badv[c] == 0; tries++) c = rndint(n);

    stamp++;
    int head = 0, tail = 0, nc = 0, cntA = 0, cntB = 0;
    rq[tail++] = c;
    mark[c] = stamp;
    while (head < tail && (cntA < k || cntB < k)) {
        int v = rq[head++];
        if (work->side[v] == 0) {
            if (cntA < k) { rr_chosen[nc++] = v; cntA++; }
        } else {
            if (cntB < k) { rr_chosen[nc++] = v; cntB++; }
        }
        for (int i = 0; i < work->deg[v]; i++) {
            int u = work->adj[v][i];
            if (mark[u] != stamp) { mark[u] = stamp; rq[tail++] = u; }
        }
    }
    if (nc == 0) return 0;

    copy_graph(&ruin_save, work);
    for (int i = 0; i < nc; i++) {
        int u = rr_chosen[i];
        while (work->deg[u] > 0) del_edge(work, u, work->adj[u][0]);
    }

    int na = 0, nb = 0;
    for (int v = 0; v < n; v++) {
        int need = d - work->deg[v];
        for (int r = 0; r < need; r++) {
            if (work->side[v] == 0) rr_astub[na++] = v;
            else rr_bstub[nb++] = v;
        }
    }
    if (na != nb || na == 0) {
        copy_graph(work, &ruin_save);
        return 0;
    }
    for (int i = na - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = rr_astub[i]; rr_astub[i] = rr_astub[j]; rr_astub[j] = t;
    }
    for (int i = nb - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = rr_bstub[i]; rr_bstub[i] = rr_bstub[j]; rr_bstub[j] = t;
    }
    for (int i = 0; i < nb; i++) rr_bused[i] = 0;
    for (int i = 0; i < na; i++) {
        int a = rr_astub[i], placed = 0;
        int off = rndint(nb);
        for (int t = 0; t < nb && !placed; t++) {
            int j = (off + t) % nb;
            if (rr_bused[j]) continue;
            int b = rr_bstub[j];
            if (has_edge(work, a, b)) continue;
            add_edge(work, a, b);
            rr_bused[j] = 1;
            placed = 1;
        }
        if (!placed) {
            copy_graph(work, &ruin_save);
            return 0;
        }
    }

    long nbad = bad_pairs(work);
    if (nbad <= *bad || rnd01() < exp(-(double)(nbad - *bad) / 0.5)) {
        *bad = nbad;
        return 1;
    }
    copy_graph(work, &ruin_save);
    return 0;
}

/* Sampled-source objective. srcs[0..ns) are source vertices; insrc marks membership.
 * F = sum over sources s of (number of vertices unreached from s within distance D).
 * F = 0 implies no bad pair touches a source; the exact check decides the rest. */
static int srcs[MAXN];
static int ns = 0;
static unsigned char insrc[MAXN];

static void clear_sources(void) {
    for (int i = 0; i < ns; i++) insrc[srcs[i]] = 0;
    ns = 0;
}

/* Add up to k new sources. If need_bad is set, prefer vertices with bad pairs (badv > 0 from the
 * last exact check). A deterministic scan finishes the job when random sampling misses. */
static void add_sources(int n, int k, int need_bad) {
    int added = 0;
    for (int tries = 0; tries < 40 * k && added < k && ns < n; tries++) {
        int v = rndint(n);
        if (insrc[v] || (need_bad && badv[v] == 0)) continue;
        insrc[v] = 1;
        srcs[ns++] = v;
        added++;
    }
    if (need_bad) {
        int off = rndint(n);
        for (int t = 0; t < n && added < k && ns < n; t++) {
            int v = (off + t) % n;
            if (insrc[v] || badv[v] == 0) continue;
            insrc[v] = 1;
            srcs[ns++] = v;
            added++;
        }
    }
}

static long sample_bad(const Graph *g) {
    long f = 0;
    for (int i = 0; i < ns; i++) f += g->n - ball_size(g, srcs[i]);
    return f;
}

/* Grow best by one vertex pair: pick the best of INIT_TRIALS greedy wirings, then repair.
 * Phase A anneals by degree-preserving swaps on the sampled objective. When F reaches zero, an
 * exact check decides; if bad pairs remain, their vertices join the source set. Phase B applies
 * ruin-and-recreate bursts when the objective has stalled for STALL_LIMIT swaps. */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound() || n + 2 > MAXN) return 0;
    static Graph trial;
    long bestbad = -1;
    for (int t = 0; t < INIT_TRIALS; t++) {
        if (!wire_greedy(best, &trial)) wire_pair(best, &trial);
        long b = bad_pairs(&trial);
        if (bestbad < 0 || b < bestbad) {
            bestbad = b;
            copy_graph(work, &trial);
        }
        if (bestbad == 0 || now() > until) break;
    }
    clear_sources();
    long bad = bad_pairs(work);
    if (bad == 0) return is_valid(work);
    add_sources(work->n, SRC_INIT / 2, 1);
    add_sources(work->n, SRC_INIT - SRC_INIT / 2, 0);

    long f = sample_bad(work);
    double T = 1.0;
    long it = 0, lastf = f, stall = 0;
    for (;;) {
        if (f == 0) {
            bad = bad_pairs(work);
            if (bad == 0) break;
            add_sources(work->n, SRC_ADD, 1);
            f = sample_bad(work);
            lastf = f;
            stall = 0;
            T = 1.0;
            continue;
        }
        if ((++it & 15) == 0 && now() > until) return 0;
        if (stall > STALL_LIMIT) {
            bad = bad_pairs(work);
            for (int r = 0; r < RR_BURST && bad > 0; r++) {
                if ((r & 3) == 0 && now() > until) return 0;
                ruin_recreate_step(work, &bad, 2 + rndint(RR_MAXK));
            }
            f = sample_bad(work);
            lastf = f;
            stall = 0;
            T = 1.0;
            continue;
        }
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
        long nf = sample_bad(work);
        /* Scale the temperature to the objective: one bad pair is about 2*ns/n units of F. */
        double sc = 2.0 * ns / (double)work->n;
        if (nf <= f || rnd01() < exp((double)(f - nf) / (T * sc))) {
            f = nf;
        } else {
            del_edge(work, v, t);
            del_edge(work, s, u);
            add_edge(work, v, u);
            add_edge(work, s, t);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
        if (f < lastf) { lastf = f; stall = 0; }
        else stall++;
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);

    if (D >= 2 && best.n < moore_bound()) {
        if (best.n < 1500) fast_lift_search(&best, t0 + (t_end - t0) * 0.8);
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


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
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

    budget = 0.92 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 3)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
