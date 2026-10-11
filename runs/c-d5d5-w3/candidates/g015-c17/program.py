"""Group-lift search with a broad pool of non-abelian base groups.

Python passes a pool of permutation groups, each given by generators on a small point set. The C
engine closes each pool entry into a multiplication table. A lift over a group G with kb base
vertices per side has 2*kb*G vertices. Left multiplication is an automorphism, so diameter <= D is
checked by BFS from 2*kb class representatives. Voltages and 2-switches are annealed on the number
of unreached pairs. Each attempt picks a pool group and the smallest base size kb that beats the
current best. Edge-splitting growth, a semidirect-product sampler (the previous engine), and a
grow-by-two repair remain as fallbacks. Python keeps K_{d,d} or a known construction as the
fallback, and every output is re-checked in C and Python.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-lift version.
 *
 * Usage:   prog d D seed time_limit [group ...]  < start_graph
 * group:   "n ng" followed by ng permutations of 0..n-1 (n integers each), generating a group
 *          acting on n points. The closure is computed here (order <= MAXG).
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
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
#define MAXK 8
#define MAXDART (MAXD * MAXK)
#define MAXG 128
#define MAXP 64
#define MAXTG 40
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

/* Table groups, built by closure from generators given on the command line. */
static int NTG = 0;
static int TG_ORD[MAXTG];
static unsigned char TG_MUL[MAXTG][MAXG * MAXG];

/* Semidirect groups Z_m x|_r Z_k2 (the previous engine's family). */
static int CUR_KIND = 0;   /* 0 = semidirect, 1 = table */
static int CUR_TG = 0;
static int GORD = 1;
static int GM = 1, GK2 = 1, GR = 0;
static int RP[MAXN];

static int gmul(int x, int y) {
    if (CUR_KIND == 1) return TG_MUL[CUR_TG][x * GORD + y];
    int a = x / GK2, b = x % GK2, c = y / GK2, e = y % GK2;
    return (int)(((long)a + (long)RP[b] * c) % GM) * GK2 + (b + e) % GK2;
}

static void set_semi(int m, int k2, int r) {
    CUR_KIND = 0;
    GM = m;
    GK2 = k2;
    GR = r;
    GORD = m * k2;
    RP[0] = 1 % m;
    for (int b = 1; b < k2; b++) RP[b] = (int)((long)RP[b - 1] * r % m);
}

static void set_table(int t) {
    CUR_KIND = 1;
    CUR_TG = t;
    GORD = TG_ORD[t];
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

static unsigned char GEN[16][MAXP];
static unsigned char GEL[MAXG][MAXP];
static uint64_t GELH[MAXG];

static uint64_t perm_hash(const unsigned char *p, int n) {
    uint64_t h = 1469598103934665603ULL;
    for (int k = 0; k < n; k++) {
        h ^= (uint64_t)(p[k] + 1);
        h *= 1099511628211ULL;
    }
    return h;
}

static int find_elem(const unsigned char *p, int n, uint64_t h, int cnt) {
    for (int q = 0; q < cnt; q++)
        if (GELH[q] == h && memcmp(GEL[q], p, (size_t)n) == 0) return q;
    return -1;
}

/* Parse "n ng" + ng permutations, close them into a group (order <= MAXG), store its table.
 * Element 0 is the identity. Returns 1 on success. */
static int parse_group_arg(const char *s) {
    if (NTG >= MAXTG) return 0;
    const char *p = s;
    char *end = NULL;
    long nl = strtol(p, &end, 10);
    if (end == p || nl < 1 || nl > MAXP) return 0;
    p = end;
    long ngl = strtol(p, &end, 10);
    if (end == p || ngl < 1 || ngl > 16) return 0;
    p = end;
    int n = (int)nl, ng = (int)ngl;
    for (int g = 0; g < ng; g++) {
        int seen[MAXP];
        for (int k = 0; k < n; k++) seen[k] = 0;
        for (int k = 0; k < n; k++) {
            long v = strtol(p, &end, 10);
            if (end == p || v < 0 || v >= n || seen[v]) return 0;
            seen[v] = 1;
            GEN[g][k] = (unsigned char)v;
            p = end;
        }
    }
    int cnt = 1;
    for (int k = 0; k < n; k++) GEL[0][k] = (unsigned char)k;
    GELH[0] = perm_hash(GEL[0], n);
    unsigned char out[MAXP];
    for (int i = 0; i < cnt; i++) {
        for (int g = 0; g < ng; g++) {
            for (int k = 0; k < n; k++) out[k] = GEN[g][GEL[i][k]];
            uint64_t h = perm_hash(out, n);
            if (find_elem(out, n, h, cnt) < 0) {
                if (cnt >= MAXG) return 0;
                memcpy(GEL[cnt], out, (size_t)n);
                GELH[cnt] = h;
                cnt++;
            }
        }
    }
    int t = NTG;
    unsigned char c[MAXP];
    for (int i = 0; i < cnt; i++)
        for (int j = 0; j < cnt; j++) {
            for (int k = 0; k < n; k++) c[k] = GEL[j][GEL[i][k]];
            int f = find_elem(c, n, perm_hash(c, n), cnt);
            if (f < 0) return 0;
            TG_MUL[t][i * cnt + j] = (unsigned char)f;
        }
    TG_ORD[t] = cnt;
    NTG++;
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

/* Saved base of the best lift so far (used by edge-splitting growth). */
static int BOK = 0, BKB = 0, BND = 0;
static int BKIND = 0, BTG = 0, BM = 1, BK2 = 1, BR = 0;
static int BDI[MAXDART], BDJ[MAXDART], BDS[MAXDART];

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
        int src = rep * GORD;   /* element 0 is the identity */
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

/* Annealing over voltages and 2-switches of DJ. Both moves keep every A- and B-degree at d.
 * On success, out holds the full lift. */
static int anneal(long steps, Graph *out) {
    long cost = orbit_cost();
    for (long s = 0; s < steps && cost > 0; s++) {
        if ((s & 31) == 0 && now() > t_end) return 0;
        double T = 2.0 * (1.0 - (double)s / (double)steps) + 0.05;
        if (rnd01() < 0.7) {
            int t = rndint(ND);
            int old = DS[t];
            int nv = rndint(GORD);
            if (nv == old) continue;
            DS[t] = nv;
            set_dart_perm(t);
            long c2 = orbit_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else { DS[t] = old; set_dart_perm(t); }
        } else {
            if (ND < 2) continue;
            int t1 = rndint(ND), t2 = rndint(ND);
            if (t1 == t2) continue;
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

/* Random base with kb vertices per side over the current group, then anneal. */
static int lift_climb(int kb, long steps, Graph *out) {
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
            DS[t] = rndint(GORD);
            set_dart_perm(t);
        }
    }
    return anneal(steps, out);
}

/* Save the current base (with its group) as the best-lift base. */
static void save_base(void) {
    BKB = KB;
    BND = ND;
    BKIND = CUR_KIND;
    BTG = CUR_TG;
    BM = GM;
    BK2 = GK2;
    BR = GR;
    BOK = 1;
    for (int t = 0; t < ND; t++) { BDI[t] = DI[t]; BDJ[t] = DJ[t]; BDS[t] = DS[t]; }
}

/* Load the saved best-lift base into the working state. */
static void load_base(void) {
    KB = BKB;
    ND = BND;
    if (BKIND == 1) set_table(BTG);
    else set_semi(BM, BK2, BR);
    for (int t = 0; t < ND; t++) {
        DI[t] = BDI[t];
        DJ[t] = BDJ[t];
        DS[t] = BDS[t];
        set_dart_perm(t);
    }
}

/* Edge-splitting growth: add one base vertex per side, keeping the group and all degrees.
 * Choose d distinct darts (A_i, B_j). Re-route each to (A_new, B_j), and add (A_i, B_new). */
static int split_base(void) {
    if (KB + 1 > MAXK || ND + d > MAXDART || ND < d) return 0;
    int pick[MAXD], np = 0;
    while (np < d) {
        int t = rndint(ND), dup = 0;
        for (int k = 0; k < np; k++)
            if (pick[k] == t) dup = 1;
        if (!dup) pick[np++] = t;
    }
    int A2 = KB, B2 = KB;
    int base = ND;
    for (int k = 0; k < d; k++) {
        int t = pick[k];
        int it = DI[t];
        DI[t] = A2;
        DS[t] = rndint(GORD);
        set_dart_perm(t);
        int nt = base + k;
        DI[nt] = it;
        DJ[nt] = B2;
        DS[nt] = rndint(GORD);
        set_dart_perm(nt);
    }
    KB++;
    ND += d;
    return 1;
}

static Graph LCAND;

/* Search loop. Each attempt is one of:
 *   - edge-splitting growth of the saved base (about 25%, when a base exists);
 *   - a pool table group, with kb chosen as the smallest base size that beats the best (about 60%);
 *   - a semidirect group sampled as in the previous engine (the rest).
 * Steps grow with consecutive failures. */
static void lift_search(Graph *best, double until) {
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        if (best->n + 2 > moore) return;
        long extra = (long)(fails / 20) * 4000;
        if (extra > 60000) extra = 60000;
        long steps = 3000 + rndint(9000) + extra;
        int before = best->n;
        double u = rnd01();
        if (BOK && u < 0.25) {
            load_base();
            if (split_base() && 2L * KB * GORD <= moore && 2L * KB * GORD <= MAXN &&
                anneal(steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND)) {
                copy_graph(best, &LCAND);
                save_base();
            }
        } else if (NTG > 0 && u < 0.85) {
            int t = rndint(NTG);
            long G = TG_ORD[t];
            long lo = (best->n + 2 + 2 * G - 1) / (2 * G);
            if (lo < 1) lo = 1;
            long hi = moore / (2 * G);
            if (hi > MAXK) hi = MAXK;
            if (hi * 2 * G > MAXN) hi = MAXN / (2 * G);
            if (lo > hi) { fails++; continue; }
            long kb = lo;
            if (hi > lo && rnd01() < 0.3) kb = lo + 1;
            set_table(t);
            if (lift_climb((int)kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND)) {
                copy_graph(best, &LCAND);
                save_base();
            }
        } else {
            int r = rndint(10);
            int kb = r < 3 ? 1 : r < 7 ? 2 : 3;
            long esc = fails > 40 ? (fails - 40) / 40 + 1 : 0;
            if (esc > 6) esc = 6;
            long G = (best->n + 2 + 2L * kb - 1) / (2L * kb) + rndint(4) + esc;
            if (G < 1) G = 1;
            if (2L * kb * G > moore || 2L * kb * G > MAXN) { fails++; continue; }
            int m, k2, rr;
            if (!sample_group((int)G, &m, &k2, &rr)) { fails++; continue; }
            set_semi(m, k2, rr);
            if (lift_climb(kb, steps, &LCAND) && LCAND.n > best->n && is_valid(&LCAND)) {
                copy_graph(best, &LCAND);
                save_base();
            }
        }
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

    for (int i = 5; i < argc; i++) parse_group_arg(argv[i]);

    if (d < 1 || D < 1 || d > MAXD) { printf("1 0\n"); return 0; }
    if (d == 1 || D < 2) { printf("2 1\n0 1\n"); return 0; }

    static Graph best, start;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    copy_graph(&start, &best);

    if (best.n < moore_bound()) {
        lift_search(&best, t0 + (t_end - t0) * 0.93);
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


def _cyc(n, cyc):
    """Permutation of range(n) that maps each listed point to the next one (a cycle)."""
    p = list(range(n))
    for i, x in enumerate(cyc):
        p[x] = cyc[(i + 1) % len(cyc)]
    return tuple(p)


def _direct_cyclic(gens, a, k):
    """Generators of G x Z_k, where G acts on a points and Z_k acts on the next k points."""
    out = [tuple(g) + tuple(range(a, a + k)) for g in gens]
    out.append(tuple(range(a)) + tuple(a + (j + 1) % k for j in range(k)))
    return out, a + k


def _affine(p, dim, mats):
    """Affine group F_p^dim semidirect <mats>, acting on the p^dim points of F_p^dim."""
    pts = list(itertools.product(range(p), repeat=dim))
    idx = {v: i for i, v in enumerate(pts)}
    gens = []
    for i in range(dim):
        e = [0] * dim
        e[i] = 1
        gens.append(tuple(idx[tuple((v[j] + e[j]) % p for j in range(dim))] for v in pts))
    for M in mats:
        gens.append(tuple(
            idx[tuple(sum(M[r][c] * v[c] for c in range(dim)) % p for r in range(dim))]
            for v in pts))
    return gens, len(pts)


def _group_args():
    """Generator strings for the C engine: "n ng" + ng permutations of n points each."""
    specs = []
    A4 = [_cyc(4, [0, 1, 2]), (1, 0, 3, 2)]
    S4 = [_cyc(4, [0, 1, 2, 3]), _cyc(4, [0, 1])]
    S3 = [_cyc(3, [0, 1, 2]), _cyc(3, [0, 1])]
    specs.append(([_cyc(5, [0, 1, 2]), _cyc(5, [0, 1, 2, 3, 4])], 5))   # A5, order 60
    specs.append(([_cyc(5, [0, 1, 2, 3, 4]), _cyc(5, [0, 1])], 5))      # S5, order 120
    for k in (2, 3, 4, 5, 6, 7, 8):
        specs.append(_direct_cyclic(A4, 4, k))                          # A4 x Z_k
    for k in (2, 3, 4, 5):
        specs.append(_direct_cyclic(S4, 4, k))                          # S4 x Z_k
    for k in (4, 5, 6, 7, 8, 9, 10):
        specs.append(_direct_cyclic(S3, 3, k))                          # S3 x Z_k
    specs.append(_affine(3, 2, [[[0, 2], [1, 0]]]))                     # 3^2 : Z4, 36
    specs.append(_affine(3, 2, [[[1, 1], [0, 1]]]))                     # Heisenberg 27
    specs.append(_affine(3, 2, [[[2, 0], [0, 2]]]))                     # 3^2 : Z2, 18
    specs.append(_affine(3, 2, [[[1, 2], [1, 1]]]))                     # AGL(1,9), 72
    specs.append(_affine(5, 2, [[[0, 4], [1, 0]]]))                     # 5^2 : Z4, 100
    specs.append(_affine(5, 2, [[[0, 4], [1, 4]]]))                     # 5^2 : Z3, 75
    specs.append(_affine(5, 2, [[[4, 0], [0, 4]]]))                     # 5^2 : Z2, 50
    specs.append(_affine(7, 2, [[[6, 0], [0, 6]]]))                     # 7^2 : Z2, 98
    specs.append(_affine(2, 3, [[[0, 0, 1], [1, 0, 1], [0, 1, 0]]]))    # 2^3 : Z7, 56
    specs.append(_affine(2, 4, [[[0, 0, 0, 1], [1, 0, 0, 1],
                                 [0, 1, 0, 1], [0, 0, 1, 1]]]))         # 2^4 : Z5, 80
    specs.append(_affine(5, 1, [[[2]]]))                                 # AGL(1,5), 20
    specs.append(_affine(7, 1, [[[3]]]))                                 # AGL(1,7), 42
    specs.append(_affine(11, 1, [[[2]]]))                                # AGL(1,11), 110
    out = []
    for gens, n in specs:
        out.append(f"{n} {len(gens)} " + " ".join(" ".join(str(x) for x in g) for g in gens))
    return out


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

    # Use most of the limit; keep a margin for compilation and process startup.
    budget = 0.95 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 0.5:
        return best
    try:
        try:
            groups = _group_args()
        except Exception:
            groups = []
        args = [d, D, seed, round(budget, 2)] + groups
        text = lib.run_c(C_SOURCE, args, stdin_graph=best, timeout=budget + 2.5)
        n, edges = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, edges, d, D):
            best = (n, edges)
    except (RuntimeError, ValueError, OSError):
        pass
    return best
