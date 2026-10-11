"""Permutation-group voltage lifts plus semidirect lifts, then grow-by-two annealing.

Changed construction: the C engine now also draws voltage groups from explicit permutation groups
(symmetric and alternating groups, PSL/PGL(2,q), direct products with cyclic groups), given as
generators on the command line. Each group is closed in C, and its multiplication table is built
on demand. Lifts over these nonabelian groups are the new search space. Semidirect Z_m x| Z_k2
lifts remain as the fallback path. Every output is re-checked in C and Python, and the Python
side keeps the Moore-type, K_{d,d}, and known-construction fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 *
 * Usage:   prog d D seed time_limit [group ...]   < start_graph
 * group:   "k/g1/g2/..." where each generator g is k comma-separated images of 0..k-1
 *          (a permutation group on k points). Groups are closed in C; order <= MAXG kept.
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1 (lift search): base with kb vertices per side, d darts out of each base vertex
 *   (layers are permutations). Dart (i, j, s) joins A_{i,g} to B_{j, g*s} for a group G.
 *   Left multiplication is an automorphism, so the diameter is <= D iff a BFS of depth D from
 *   each of the 2kb class representatives reaches everything. Voltages and layer swaps are
 *   annealed on the number of unreached pairs. Groups come from the permutation list or from
 *   semidirect products Z_m x| Z_k2.
 * Phase 2 (grow by two): add one vertex per side, then anneal degree-preserving edge swaps.
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
#define MAXG 1100
#define MAXPG 256
#define MAXPK 16
#define HSIZE 8192

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

/* Current group: order GORD, multiplication table GT[x*GORD+y] = x*y, identity 0. */
static int GORD = 1;
static int GT[MAXG * MAXG];
static int CUR_ID = -3;   /* -1 semidirect, >= 0 permutation group index, -3 none */

/* Semidirect Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
static int GM, GK2;
static int RP[MAXN];

static int gmul(int x, int y) {
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

static void set_semidirect(int m, int k2, int r) {
    GM = m;
    GK2 = k2;
    int G = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) GT[x * G + y] = gmul(x, y);
    GORD = G;
    CUR_ID = -1;
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

/* Hash table keyed by permutation codes (4 bits per point, k <= 16). */
static uint64_t HKEY[HSIZE];
static int HVAL[HSIZE], HSTAMP[HSIZE];
static int HCUR = 1;

static void h_clear(void) { HCUR++; }

static int h_slot(uint64_t key) {
    unsigned h = (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
    while (HSTAMP[h] == HCUR && HKEY[h] != key) h = (h + 1) & (HSIZE - 1);
    return (int)h;
}

static int h_lookup(uint64_t key) {
    int s = h_slot(key);
    return HSTAMP[s] == HCUR ? HVAL[s] : -1;
}

static void h_insert(uint64_t key, int val) {
    int s = h_slot(key);
    HSTAMP[s] = HCUR;
    HKEY[s] = key;
    HVAL[s] = val;
}

static uint64_t pcode(const unsigned char *p, int k) {
    uint64_t c = 0;
    for (int i = 0; i < k; i++) c |= (uint64_t)p[i] << (4 * i);
    return c;
}

typedef struct {
    int k, G;
    unsigned char el[MAXG][MAXPK];
} PGroup;

static PGroup PG[MAXPG];
static int NPG = 0;

/* Closes the generators (right multiplication) into P. Returns 0 if order exceeds MAXG. */
static int close_group(PGroup *P, int k, int ng, unsigned char gens[][MAXPK]) {
    h_clear();
    P->k = k;
    P->G = 1;
    for (int i = 0; i < MAXPK; i++) P->el[0][i] = (unsigned char)(i < k ? i : 0);
    h_insert(pcode(P->el[0], k), 0);
    for (int idx = 0; idx < P->G; idx++) {
        for (int g = 0; g < ng; g++) {
            unsigned char q[MAXPK];
            for (int i = 0; i < k; i++) q[i] = P->el[idx][gens[g][i]];
            uint64_t c = pcode(q, k);
            if (h_lookup(c) >= 0) continue;
            if (P->G >= MAXG) return 0;
            for (int i = 0; i < k; i++) P->el[P->G][i] = q[i];
            h_insert(c, P->G);
            P->G++;
        }
    }
    return 1;
}

static void build_perm_table(int id) {
    PGroup *P = &PG[id];
    int G = P->G, k = P->k;
    h_clear();
    for (int x = 0; x < G; x++) h_insert(pcode(P->el[x], k), x);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++) {
            unsigned char q[MAXPK];
            for (int i = 0; i < k; i++) q[i] = P->el[x][P->el[y][i]];
            int z = h_lookup(pcode(q, k));
            GT[x * G + y] = z < 0 ? 0 : z;
        }
    GORD = G;
}

static void set_perm(int id) {
    if (CUR_ID == id) return;
    build_perm_table(id);
    CUR_ID = id;
}

/* Parses "k/g1/g2/..." (each gi = k comma-separated images) and closes it into PG. */
static int parse_group(const char *s) {
    unsigned char gens[16][MAXPK];
    int ng = 0;
    char *e;
    if (NPG >= MAXPG) return 0;
    long v = strtol(s, &e, 10);
    if (e == s || *e != '/' || v < 1 || v > MAXPK) return 0;
    int k = (int)v;
    const char *p = e + 1;
    while (*p) {
        if (ng >= 16) return 0;
        int seen[MAXPK];
        memset(seen, 0, sizeof seen);
        for (int i = 0; i < k; i++) {
            long x = strtol(p, &e, 10);
            if (e == p || x < 0 || x >= k || seen[x]) return 0;
            seen[x] = 1;
            gens[ng][i] = (unsigned char)x;
            p = e;
            if (i < k - 1) {
                if (*p != ',') return 0;
                p++;
            } else {
                if (*p == '/') p++;
                else if (*p != '\0') return 0;
            }
        }
        ng++;
    }
    if (ng == 0) return 0;
    if (!close_group(&PG[NPG], k, ng, gens)) return 0;
    NPG++;
    return 1;
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
    for (int g = 0; g < GORD; g++) DPERM[t][g] = GT[g * GORD + DS[t]];
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

/* One annealing run over voltages and layer swaps, for the group currently set.
 * On success, out holds the full lift. */
static int lift_climb(int kb, long steps, Graph *out) {
    int G = GORD;
    KB = kb;
    ND = d * kb;
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

/* Group search: with probability 0.6, a permutation group whose order is near the
 * needed value is used; otherwise a semidirect group. The needed order rises with
 * failures (escalation). */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        int r = rndint(10);
        int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
        long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
        if (esc > 6) esc = 6;
        long Gmin = (best->n + 2 + 2L * kb - 1) / (2L * kb);
        if (Gmin < 1) Gmin = 1;
        int id = -1;
        if (NPG > 0 && rnd01() < 0.6) {
            int cand[MAXPG], nc = 0;
            long hi = Gmin + 8 + 2 * esc;
            for (int i = 0; i < NPG; i++) {
                long G = PG[i].G;
                if (G >= Gmin && G <= hi && 2L * kb * G <= moore && 2L * kb * G <= MAXN)
                    cand[nc++] = i;
            }
            if (nc > 0) id = cand[rndint(nc)];
        }
        if (id >= 0) {
            set_perm(id);
        } else {
            long G = Gmin + rndint(4) + esc;
            if (G > MAXG || 2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
            int m, k2, rr;
            if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
            set_semidirect(m, k2, rr);
        }
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        if (lift_climb(kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND))
            copy_graph(best, &LCAND);
        fails = best->n > before ? 0 : fails + 1;
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
        fprintf(stderr, "usage: %s d D seed time_limit [groups...] < start_graph\n", argv[0]);
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

    for (int a = 5; a < argc; a++) parse_group(argv[a]);

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.9);
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) copy_graph(&best, &start);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4, degree q+1."""
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
        return lib.projective_plane_incidence(d - 1)   # Moore graph
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    if D == 4:
        for q in range(min(d - 1, 7), 1, -1):
            if lib.is_prime_power(q) and q + 1 <= d:
                return _gq_w(q)
    return None


def _cyc(n, cycle):
    """Permutation list on n points sending cycle[i] to cycle[i+1] (cyclically)."""
    p = list(range(n))
    for a, b in zip(cycle, cycle[1:] + cycle[:1]):
        p[a] = b
    return p


def _sym(n):
    return n, [_cyc(n, (i, i + 1)) for i in range(n - 1)]


def _alt(n):
    return n, [_cyc(n, (i, i + 1, i + 2)) for i in range(n - 2)]


def _psl_pgl(q, squares):
    """PSL(2,q) (squares=True) or PGL(2,q) acting on the projective line (q+1 points, point q = infinity)."""
    F = lib.GF(q)
    g = F.primitive_element()
    h = F.mul(g, g) if squares else g
    t_add = [F.add(x, 1) for x in range(q)] + [q]
    t_mul = [F.mul(h, x) for x in range(q)] + [q]
    t_inv = [q] + [F.neg(F.inv(x)) for x in range(1, q)] + [0]
    return q + 1, [t_add, t_mul, t_inv]


def _direct(A, B):
    """Direct product of two permutation groups acting on disjoint point sets."""
    ka, ga = A
    kb, gb = B
    gens = [p + list(range(ka, ka + kb)) for p in ga]
    gens += [list(range(ka)) + [ka + x for x in p] for p in gb]
    return ka + kb, gens


def _perm_specs():
    """Permutation-group specs, as strings "k/gen/gen/...", for the C engine to close and use."""
    base = {
        "S3": _sym(3), "S4": _sym(4), "S5": _sym(5), "A4": _alt(4), "A5": _alt(5),
        "A6": _alt(6), "L24": _psl_pgl(4, True), "L25": _psl_pgl(5, True),
        "G25": _psl_pgl(5, False), "L27": _psl_pgl(7, True), "G27": _psl_pgl(7, False),
        "L28": _psl_pgl(8, True), "L29": _psl_pgl(9, True), "G29": _psl_pgl(9, False),
        "L211": _psl_pgl(11, True),
    }
    specs = list(base.values())
    for name in base:
        k0 = base[name][0]
        for c in range(2, 13):
            if k0 + c <= 16:
                specs.append(_direct(base[name], (c, [_cyc(c, tuple(range(c)))])))
    small = ["S3", "S4", "A4", "A5", "S5", "L27", "L25"]
    for i, a in enumerate(small):
        for b in small[i:]:
            if base[a][0] + base[b][0] <= 16:
                specs.append(_direct(base[a], base[b]))
    out = []
    for k, gens in specs:
        if k > 16:
            continue
        out.append(f"{k}" + "".join("/" + ",".join(map(str, p)) for p in gens))
    return out[:200]


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

    if best[0] >= lib.moore_bound(d, D):
        return best

    try:
        groups = _perm_specs() if D >= 3 else []
    except Exception:
        groups = []

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.95 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)] + groups,
                         stdin_graph=best, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
