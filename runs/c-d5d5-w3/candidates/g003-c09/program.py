"""Bold variant: non-semidirect Cayley (Haar-type) bipartite lifts, then the C engine.

Schedule (per case, inside time_limit):
  A. C engine from the best known start (about 50% of the budget).
  B. Python Cayley search over non-semidirect groups (about 25%): for a group G and d
     distinct elements S, the bipartite graph a_g ~ b_{g s} (s in S) is d-regular and
     vertex-transitive via left multiplication, so two BFS runs (from a_e and b_e) decide
     the diameter. Groups tried: A5 x Z_k, S4 x Z_k, A4 x Z_k, dihedral D_m x Z_k,
     A4 x A4 x Z_k, A5 x Z_2 x Z_k and non-cyclic abelian Z_a x Z_b. Orders are tried in
     ascending order, each must beat the current best, and S is hill-climbed by annealing.
  C. C engine again from the best graph so far (remaining budget): semidirect lifts,
     signed doubling and grow-by-two.
Every candidate is checked with lib.is_valid before it is accepted; K_{d,d} or the known
construction is always kept as the fallback.
"""
import math
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): base with kb vertices per side, d darts out of each base vertex
 *   (layers are permutations, so the lift is d-regular). Dart (i, j, s) joins A_{i,g} to
 *   B_{j,g*s}. Left multiplication is an automorphism, so the diameter is <= D iff a BFS of
 *   depth D from each of the 2kb class representatives reaches everything. Voltages and
 *   layer swaps are hill-climbed with annealing on the number of unreached pairs.
 *   Escalations when stuck: (a) annealing runs get more steps, (b) the target group order
 *   is raised by one step per block of failures (group-order escalation).
 * Phase 2 (signed 2-lift): double the best graph with random edge signs, then anneal the
 *   signs on the number of pairs at distance > D. Only tried while 2n <= Moore bound.
 * Phase 3 (grow by two): add one vertex per side, then anneal degree-preserving edge swaps.
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
#define MAXK 4
#define MAXDART (MAXD * MAXK)
#define BIGCOST 1000000000L

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double t_end;

/* ------------------------------------------------------------ utilities */

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

/* Upper bound on the order of a bipartite graph with max degree d and diameter D. */
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

/* ------------------------------------------------------------ graph basics */

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

/* ------------------------------------------------------------ distance check */

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D. Zero means diameter <= D. */
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

/* ------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK2, GORD;
static int RP[MAXN]; /* RP[b] = r^b mod m */

static void set_group(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

/* Random semidirect group of order G (reservoir over sampled candidates). */
static int sample_group(int G, int *om, int *ok2, int *orr) {
    int cnt = 0;
    for (int m = 1; m <= G; m++) {
        if (G % m) continue;
        int k2 = G / m;
        if (m == 1) {
            if (rndint(++cnt) == 0) { *om = 1; *ok2 = k2; *orr = 0; }
            continue;
        }
        if (k2 == 1) {
            if (rndint(++cnt) == 0) { *om = m; *ok2 = 1; *orr = 1; }
            continue;
        }
        for (int t = 0; t < 120; t++) {
            int r = 1 + rndint(m - 1);
            if (gcd(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
            if (rndint(++cnt) == 0) { *om = m; *ok2 = k2; *orr = r; }
        }
    }
    return cnt > 0;
}

/* ------------------------------------------------------------ voltage lifts */

static int KB, ND;                 /* base vertices per side, number of darts */
static int DI[MAXDART], DJ[MAXDART], DS[MAXDART];
static int DPERM[MAXDART][MAXN];   /* DPERM[t][g] = g * DS[t] */
static int LADJ[MAXN][MAXD];
static int LDEG[MAXN];
static int VIS[MAXN], VST = 0;
static int QU[MAXN];

static void set_dart_perm(int t) {
    for (int g = 0; g < GORD; g++) DPERM[t][g] = gmul(g, DS[t]);
}

static int has_dup(void) {
    for (int t1 = 0; t1 < ND; t1++)
        for (int t2 = t1 + 1; t2 < ND; t2++)
            if (DI[t1] == DI[t2] && DJ[t1] == DJ[t2] && DS[t1] == DS[t2]) return 1;
    return 0;
}

static void build_ladj(void) {
    int N = 2 * KB * GORD;
    for (int v = 0; v < N; v++) LDEG[v] = 0;
    for (int t = 0; t < ND; t++)
        for (int g = 0; g < GORD; g++) {
            int a = DI[t] * GORD + g;
            int b = (KB + DJ[t]) * GORD + DPERM[t][g];
            LADJ[a][LDEG[a]++] = b;
            LADJ[b][LDEG[b]++] = a;
        }
}

/* Unreached (representative, vertex) pairs over the 2KB class representatives. */
static long orbit_cost(void) {
    if (has_dup()) return BIGCOST;
    build_ladj();
    int N = 2 * KB * GORD;
    long total = 0;
    for (int rep = 0; rep < 2 * KB; rep++) {
        int src = rep * GORD;
        VST++;
        int head = 0, tail = 0;
        VIS[src] = VST;
        QU[tail++] = src;
        for (int depth = 0; depth < D; depth++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = QU[head++];
                for (int i = 0; i < LDEG[u]; i++) {
                    int v = LADJ[u][i];
                    if (VIS[v] != VST) { VIS[v] = VST; QU[tail++] = v; }
                }
            }
        }
        total += N - tail;
    }
    return total;
}

static void build_full(Graph *g) {
    int N = 2 * KB * GORD;
    g->n = N;
    for (int v = 0; v < N; v++) { g->deg[v] = 0; g->side[v] = v >= KB * GORD; }
    for (int t = 0; t < ND; t++)
        for (int x = 0; x < GORD; x++)
            add_edge(g, DI[t] * GORD + x, (KB + DJ[t]) * GORD + DPERM[t][x]);
}

/* One annealing run over voltages and layer swaps for a random base and the given group.
 * On success, out holds the full lift. */
static int lift_climb(int kb, int G, int m, int k2, int r, long steps, Graph *out) {
    KB = kb;
    ND = d * kb;
    set_group(m, k2, r);
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < kb; i++) perm[i] = i;
        for (int i = kb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < kb; i++) {
            int t = l * kb + i;
            DI[t] = i;
            DJ[t] = perm[i];
            DS[t] = rndint(G);
            set_dart_perm(t);
        }
    }
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(G);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart_perm(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart_perm(t); }
        } else {
            if (kb < 2) continue;
            int l = rndint(d);
            int i1 = rndint(kb), i2 = rndint(kb);
            if (i1 == i2) continue;
            int t1 = l * kb + i1, t2 = l * kb + i2;
            int tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp;
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { tmp = DJ[t1]; DJ[t1] = DJ[t2]; DJ[t2] = tmp; }
        }
    }
    if (cost != 0) return 0;
    build_full(out);
    return 1;
}

static Graph LCAND;

/* Group-order escalation: after many failed attempts, the target group order rises,
 * one step per block of 40 failures, capped at 6. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;   /* consecutive attempts that did not improve best */
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long G = (best->n + 2 + 2L * kb - 1) / (2L * kb) + rndint(4) + esc;
        if (G < 1) G = 1;
        if (2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
        int m, k2, rr;
        if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
        /* When lifts stop improving, give each annealing run more steps. */
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, (int)G, m, k2, rr, steps, &LCAND) &&
            LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
    }
}

/* ------------------------------------------------------------ signed 2-lift */

/* Edge list of the base graph (u < v), and their signs. */
static int EU[MAXN * MAXD / 2], EV[MAXN * MAXD / 2];

/* Double cover: copies u and u+n keep the side of u. Sign 0 joins u0-v0 and u1-v1;
 * sign 1 joins u0-v1 and u1-v0. Degrees and bipartiteness are preserved. */
static void build_signed(const Graph *base, int ne, const unsigned char *sg, Graph *out) {
    int n = base->n;
    out->n = 2 * n;
    for (int v = 0; v < n; v++) {
        out->deg[v] = out->deg[v + n] = 0;
        out->side[v] = out->side[v + n] = base->side[v];
    }
    for (int e = 0; e < ne; e++) {
        int u = EU[e], v = EV[e];
        if (sg[e]) { add_edge(out, u, v + n); add_edge(out, u + n, v); }
        else       { add_edge(out, u, v);     add_edge(out, u + n, v + n); }
    }
}

/* Repeated signed doubling. Each round doubles the best graph if annealing the signs
 * reaches diameter <= D. Runs only while 2n is within the Moore bound. */
static void signed_search(Graph *best, double until) {
    static Graph cand;
    static unsigned char sg[MAXN * MAXD / 2];
    while (now() < until) {
        int n = best->n;
        if (2 * n > moore_bound() || 2 * n > MAXN) return;
        int ne = 0;
        for (int u = 0; u < n; u++)
            for (int i = 0; i < best->deg[u]; i++) {
                int v = best->adj[u][i];
                if (u < v) {
                    EU[ne] = u;
                    EV[ne] = v;
                    sg[ne] = (unsigned char)rndint(2);
                    ne++;
                }
            }
        if (ne == 0) return;
        build_signed(best, ne, sg, &cand);
        long cost = bad_pairs(&cand);
        long steps = 1500 + rndint(3000);
        for (long s = 0; s < steps && cost > 0; s++) {
            if ((s & 7) == 0 && now() > until) break;
            int e = rndint(ne);
            sg[e] ^= 1;
            build_signed(best, ne, sg, &cand);
            long c2 = bad_pairs(&cand);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / 0.5)) cost = c2;
            else sg[e] ^= 1;
        }
        if (cost == 0) {
            build_signed(best, ne, sg, &cand);
            if (is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ grow by two */

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
    while (now() < until && best->n + 2 <= moore_bound() && best->n + 2 <= MAXN) {
        double left = until - now();
        double slice = left < 4.0 ? left : (left / 4 > 4.0 ? left / 4 : 4.0);
        if (grow_once(best, &work, now() + slice)) copy_graph(best, &work);
    }
}

/* ------------------------------------------------------------ main */

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
    t_end = t0 + limit * 0.97;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        double span = t_end - t0;
        lift_search(&best, t0 + span * 0.85);
        signed_search(&best, t0 + span * 0.90);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


# ---------------------------------------------------------------- known constructions

def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
    import itertools
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


def known_start(d, D):
    """Best known construction Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


# ---------------------------------------------------------------- permutation groups

def _compose(p, q):
    """Permutation p after q: i -> p[q[i]]."""
    return tuple(p[i] for i in q)


def _part_info(part):
    """Return (number of points, generators on local points) for a group factor."""
    kind = part[0]
    if kind == "A5":
        return 5, [(1, 2, 3, 4, 0), (1, 2, 0, 3, 4)]
    if kind == "A4":
        return 4, [(1, 2, 0, 3), (1, 0, 3, 2)]
    if kind == "S4":
        return 4, [(1, 2, 3, 0), (1, 0, 2, 3)]
    if kind == "D":
        m = part[1]
        return m, [tuple((i + 1) % m for i in range(m)), tuple((-i) % m for i in range(m))]
    k = part[1]  # cyclic factor "Z"
    return k, [tuple((i + 1) % k for i in range(k))]


def _part_order(part):
    kind = part[0]
    if kind == "A5":
        return 60
    if kind == "A4":
        return 12
    if kind == "S4":
        return 24
    if kind == "D":
        return 2 * part[1]
    return part[1]


def _build_group(spec, limit):
    """Return (elements, index dict, inverse index list) of the group, or None if it exceeds limit."""
    size = sum(_part_info(p)[0] for p in spec)
    gens, off = [], 0
    for p in spec:
        sz, local = _part_info(p)
        for g in local:
            full = list(range(size))
            for i in range(sz):
                full[off + i] = off + g[i]
            gens.append(tuple(full))
        off += sz
    e = tuple(range(size))
    elts, idx = [e], {e: 0}
    k = 0
    while k < len(elts):
        x = elts[k]
        k += 1
        for g in gens:
            y = _compose(x, g)
            if y not in idx:
                if len(elts) >= limit:
                    return None
                idx[y] = len(elts)
                elts.append(y)
    inv = []
    for x in elts:
        ip = [0] * size
        for i, v in enumerate(x):
            ip[v] = i
        inv.append(idx[tuple(ip)])
    return elts, idx, inv


class _Cayley:
    """Bipartite Cayley-type graph: a_g ~ b_{g s} for s in S, on vertices a_g = g, b_h = N + h."""

    def __init__(self, elts, idx, inv):
        self.elts, self.idx, self.inv = elts, idx, inv
        self.N = len(elts)
        self.cache = {}

    def table(self, s):
        t = self.cache.get(s)
        if t is None:
            es = self.elts[s]
            idx = self.idx
            t = [idx[_compose(x, es)] for x in self.elts]
            self.cache[s] = t
        return t

    def unreached(self, S, D):
        """Unreached (source, vertex) pairs from a_e and b_e within depth D. Zero iff diameter <= D."""
        N = self.N
        Rs = [self.table(s) for s in S]
        Ris = [self.table(self.inv[s]) for s in S]
        tot = 0
        for src in (0, N):
            seen = bytearray(2 * N)
            seen[src] = 1
            frontier = [src]
            reached = 1
            for _ in range(D):
                if not frontier:
                    break
                nxt = []
                for v in frontier:
                    if v < N:
                        for r in Rs:
                            w = N + r[v]
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                    else:
                        h = v - N
                        for r in Ris:
                            w = r[h]
                            if not seen[w]:
                                seen[w] = 1
                                nxt.append(w)
                reached += len(nxt)
                frontier = nxt
            tot += 2 * N - reached
        return tot


def _find_S(grp, d, D, rng, deadline):
    """Hill-climb (annealing) a d-subset S of the group until the Cayley graph has diameter <= D."""
    N = grp.N
    while time.monotonic() < deadline:
        S = rng.sample(range(N), d)
        cur = grp.unreached(S, D)
        if cur == 0:
            return S
        T = 1.0
        for step in range(3000):
            if (step & 15) == 0 and time.monotonic() > deadline:
                return None
            i = rng.randrange(d)
            new = rng.randrange(N)
            if new in S:
                continue
            S2 = S[:]
            S2[i] = new
            c2 = grp.unreached(S2, D)
            if c2 <= cur or rng.random() < math.exp(-(c2 - cur) / T):
                S, cur = S2, c2
                if cur == 0:
                    return S
            T = max(0.05, T * 0.999)
    return None


def _candidate_specs(nmin, nmax, rng):
    """Non-semidirect group specs with order in [nmin, nmax], at most two per order, ascending."""
    if nmax < nmin or nmax < 2:
        return []
    nonab = [("A5",), ("S4",), ("A4",)] + [("D", m) for m in range(3, nmax // 2 + 1)]
    specs = []
    for a in nonab:
        oa = _part_order(a)
        if nmin <= oa <= nmax:
            specs.append((oa, (a,)))
        for k in range(2, nmax // oa + 1):
            if nmin <= oa * k <= nmax:
                specs.append((oa * k, (a, ("Z", k))))
            for k2 in range(2, nmax // (2 * oa * k) + 1) if oa * 2 * k <= nmax else []:
                if nmin <= oa * 2 * k * k2 <= nmax:
                    specs.append((oa * 2 * k * k2, (a, ("Z", 2), ("Z", k), ("Z", k2))))
        for k in range(2, nmax // (2 * oa) + 1):
            if nmin <= 2 * oa * k <= nmax:
                specs.append((2 * oa * k, (a, ("Z", 2), ("Z", k))))
    for a in range(2, nmax + 1):
        for b in range(a, nmax // a + 1):
            if math.gcd(a, b) > 1 and nmin <= a * b <= nmax:
                specs.append((a * b, (("Z", a), ("Z", b))))
    rng.shuffle(specs)
    specs.sort(key=lambda t: t[0])
    chosen, per = [], {}
    for o, sp in specs:
        if per.get(o, 0) >= 2:
            continue
        per[o] = per.get(o, 0) + 1
        chosen.append((o, sp))
    return chosen


def _cayley_search(d, D, nmin, nmax, deadline, rng):
    """Try non-semidirect groups in ascending order; return the largest valid (n, edges) found, or None."""
    best = None
    lo = nmin
    for o, spec in _candidate_specs(nmin, nmax, rng):
        now = time.monotonic()
        if now >= deadline:
            break
        if o < lo:
            continue
        data = _build_group(spec, nmax + 1)
        if data is None:
            continue
        grp = _Cayley(*data)
        N = grp.N
        if N < lo or N > nmax or N < d:
            continue
        S = _find_S(grp, d, D, rng, min(deadline, now + 3.0))
        if S is None:
            continue
        edges = []
        for s in S:
            tbl = grp.table(s)
            edges.extend((g, N + tbl[g]) for g in range(N))
        if lib.is_valid(2 * N, edges, d, D):
            best = (2 * N, edges)
            lo = N + 1
    return best


# ---------------------------------------------------------------- driver

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))          # K_{d,d}: valid for D >= 2
    try:
        start = known_start(d, D)
    except (ValueError, RuntimeError):
        start = None
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    end = t0 + 0.95 * time_limit - 1.0
    total = end - time.monotonic()
    if total < 1.5:
        return best
    rng = random.Random(seed * 7919 + 13)

    def run_engine(graph, seconds):
        if seconds < 0.5:
            return None
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(seconds, 2)],
                             stdin_graph=graph, timeout=seconds + 2.5)
            n, edges = lib.parse_graph_text(text)
            if n > graph[0] and lib.is_valid(n, edges, d, D):
                return (n, edges)
        except (RuntimeError, ValueError, OSError):
            pass
        return None

    # Phase A: C engine from the best known start.
    r = run_engine(best, 0.50 * total)
    if r is not None:
        best = r

    # Phase B: non-semidirect Cayley search for graphs larger than the current best.
    try:
        cay = _cayley_search(d, D, best[0] // 2 + 1, moore // 2,
                             time.monotonic() + 0.25 * total, rng)
        if cay is not None and cay[0] > best[0] and lib.is_valid(cay[0], cay[1], d, D):
            best = cay
    except Exception:
        pass

    # Phase C: C engine again from the best graph, with whatever time remains.
    remaining = end - time.monotonic() - 0.5
    r = run_engine(best, remaining)
    if r is not None:
        best = r

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
