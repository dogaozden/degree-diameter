"""Group-lift search, edition 2.

Bi-Cayley lifts over a pool of finite groups that the previous program did not use:
affine groups F_q x| H (q a prime power, so the additive group can be non-cyclic),
permutation groups (A5, S5, PSL(2,7)), and semidirect products Z_m x| Z_k.
Python sends the group tables and the start graph to C through the graph channel of
lib.run_c. C anneals voltages for k = 1..4 base vertices per side, then grows the
best graph by two. Falls back to K_{d,d} if anything fails.
"""
import math
import random
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core, group-lift edition.
 *
 * Usage:  prog d D seed time_limit < payload
 * stdin:  "n m" then m lines "u v". The m pairs form a flat int payload:
 *   [G, (N_1, table_1: N_1*N_1 ints), ..., G-th group,  start_n, start_m, start_edges]
 *   table[x*N+y] = x*y, identity = 0. start_edges has 2*start_m ints.
 *   A start with start_n = 0 is allowed (then K_{d,d} is used).
 * stdout: "n m" then m lines "u v" for the best valid graph found.
 *
 * Phase 1: bi-Cayley lifts over the group pool. Vertices A(i,x), B(j,x), i,j < k, x in G.
 *   Dart (i,j,g) gives edges A(i,x) ~ B(j, x*g). Left multiplication is an automorphism,
 *   so diameter <= D is equivalent to: BFS from the 2k identity vertices reaches all.
 *   Simulated annealing over dart targets and per-layer matchings.
 * Phase 2: grow by two from the best graph (stolen edges + annealed swaps).
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
#define MAXGRP 64
#define MAXGN 1024

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int N;
    int *mt;
} Group;

static int d, D;
static double t_end;
static long moore;
static Graph best;

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

/* ------------------------------------------------------------------ payload */

static int *PAY = NULL;
static long PAYLEN = 0;
static Group groups[MAXGRP];
static int NG = 0;
static long START_P = 0;

static int read_payload(void) {
    long n, m;
    if (scanf("%ld %ld", &n, &m) != 2 || m < 0 || m > 50000000L) { PAYLEN = 0; return 0; }
    PAYLEN = 2 * m;
    PAY = (int *)malloc(sizeof(int) * (size_t)(PAYLEN + 1));
    if (!PAY) { PAYLEN = 0; return 0; }
    for (long e = 0; e < m; e++) {
        if (scanf("%d %d", &PAY[2 * e], &PAY[2 * e + 1]) != 2) { PAYLEN = 0; return 0; }
    }
    return 1;
}

static int seenG[MAXGN];
static int seenStamp = 0;

static void parse_groups(void) {
    long p = 0;
    NG = 0;
    START_P = PAYLEN;
    if (PAYLEN < 1) return;
    long G = PAY[p++];
    for (long g = 0; g < G; g++) {
        if (p >= PAYLEN) return;
        long N = PAY[p++];
        if (N < 1 || N > MAXGN || p + N * N > PAYLEN) return;
        const int *T = PAY + p;
        int ok = 1;
        for (long x = 0; x < N && ok; x++) {
            seenStamp++;
            for (long y = 0; y < N; y++) {
                int v = T[x * N + y];
                if (v < 0 || v >= N || seenG[v] == seenStamp) { ok = 0; break; }
                seenG[v] = seenStamp;
            }
        }
        for (long y = 0; y < N && ok; y++)
            if (T[y] != y || T[y * N] != y) ok = 0;
        if (ok && NG < MAXGRP) {
            groups[NG].N = (int)N;
            groups[NG].mt = (int *)malloc(sizeof(int) * (size_t)(N * N));
            if (groups[NG].mt) {
                memcpy(groups[NG].mt, T, sizeof(int) * (size_t)(N * N));
                NG++;
            }
        }
        p += N * N;
    }
    START_P = p;
}

static void load_start(Graph *g) {
    g->n = 0;
    long p = START_P;
    if (p + 2 > PAYLEN) return;
    long sn = PAY[p], sm = PAY[p + 1];
    p += 2;
    if (sn <= 0 || sn > MAXN || sm < 0 || p + 2 * sm > PAYLEN) return;
    g->n = (int)sn;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (long e = 0; e < sm; e++) {
        int u = PAY[p + 2 * e], v = PAY[p + 2 * e + 1];
        if (u < 0 || v < 0 || u >= g->n || v >= g->n || u == v ||
            g->deg[u] >= MAXD || g->deg[v] >= MAXD) { g->n = 0; return; }
        add_edge(g, u, v);
    }
    static int queue[MAXN];
    for (int s = 0; s < g->n; s++) {
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

/* ------------------------------------------------------------------ lifts */

static int K_;
static int ND_;
static int dI[MAXDART], dJ[MAXDART], dG[MAXDART];
static int adjL[MAXN][MAXD];
static int cntL[MAXN];
static int visL[MAXN];
static int qL[MAXN];
static int stampL = 0;

static const int *MT = NULL;
static int GN = 0;

static void select_group(int gi) {
    GN = groups[gi].N;
    MT = groups[gi].mt;
}

/* Cost = 1e6 * duplicate darts + total unreached (representative, vertex) pairs. */
static long lift_cost(void) {
    int k = K_, N = GN, n = 2 * k * N;
    long pen = 0;
    for (int t = 0; t < ND_; t++)
        for (int u = 0; u < t; u++)
            if (dI[t] == dI[u] && dJ[t] == dJ[u] && dG[t] == dG[u]) pen++;
    for (int v = 0; v < n; v++) cntL[v] = 0;
    for (int t = 0; t < ND_; t++)
        for (int x = 0; x < N; x++) {
            int a = dI[t] * N + x;
            int b = (k + dJ[t]) * N + MT[x * N + dG[t]];
            adjL[a][cntL[a]++] = b;
            adjL[b][cntL[b]++] = a;
        }
    long unreached = 0;
    int reps[2 * MAXK], nr = 0;
    for (int i = 0; i < k; i++) reps[nr++] = i * N;
    for (int j = 0; j < k; j++) reps[nr++] = (k + j) * N;
    for (int r = 0; r < nr; r++) {
        stampL++;
        int head = 0, tail = 0, src = reps[r];
        visL[src] = stampL;
        qL[tail++] = src;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qL[head++];
                for (int i = 0; i < cntL[u]; i++) {
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
    int k = K_, N = GN;
    g->n = 2 * k * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= k * N; }
    for (int t = 0; t < ND_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dI[t] * N + x, (k + dJ[t]) * N + MT[x * N + dG[t]]);
}

/* Each B vertex gets exactly one dart from every layer, so all degrees equal d. */
static void random_darts(void) {
    int k = K_;
    ND_ = k * d;
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
            dG[t] = rndint(GN);
        }
    }
}

static int lift_attempt(int steps, double until) {
    random_darts();
    long c = lift_cost();
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 511) == 0 && now() > until) break;
        double T = 1.5 * (1.0 - (double)s / steps) + 0.05;
        if (K_ > 1 && rnd01() < 0.3) {
            int l = rndint(d), a = rndint(K_), b = rndint(K_);
            if (a == b) continue;
            int t1 = l * K_ + a, t2 = l * K_ + b;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else { tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp; }
        } else {
            int t = rndint(ND_);
            int old = dG[t];
            dG[t] = rndint(GN);
            long c2 = lift_cost();
            if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
            else dG[t] = old;
        }
    }
    return c == 0;
}

/* Feasible groups for k base vertices per side with lift order in [T, moore].
   Biased toward the smallest feasible orders, which are the most likely to succeed. */
static int pick_group(int k, long T) {
    int cand[MAXGRP], nc = 0;
    for (int gi = 0; gi < NG; gi++) {
        long n2 = 2L * k * groups[gi].N;
        if (n2 >= T && n2 <= moore && n2 <= MAXN) cand[nc++] = gi;
    }
    if (nc == 0) return -1;
    for (int i = 1; i < nc; i++) {
        int x = cand[i], j = i - 1;
        while (j >= 0 && groups[cand[j]].N > groups[x].N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = x;
    }
    double u = rnd01();
    int idx = (int)(nc * u * u);
    if (idx >= nc) idx = nc - 1;
    return cand[idx];
}

static void lift_phase(double until) {
    static Graph cand;
    int fails = 0;
    while (now() < until && best.n < moore) {
        int k = 1 + rndint(MAXK);
        int gi = pick_group(k, (long)best.n + 1);
        if (gi < 0) {
            if (++fails > 100000) return;
            continue;
        }
        select_group(gi);
        K_ = k;
        if (lift_attempt(30000, until)) {
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
        fprintf(stderr, "usage: %s d D seed time_limit < payload\n", argv[0]);
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
    t_end = t0 + limit * 0.93 - 0.3;
    if (t_end < t0) t_end = t0;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    best.n = 0;
    if (read_payload()) {
        parse_groups();
        load_start(&best);
    }
    if (best.n == 0) complete_bipartite(&best);

    if (best.n < moore && NG > 0)
        lift_phase(t0 + (t_end - t0) * 0.8);
    if (best.n < moore)
        grow_search(t_end);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Permutation generators for small non-solvable groups (points 0..n-1).
_PSL27_T = tuple([(x + 1) % 7 for x in range(7)] + [7])
_PSL27_M = tuple([(2 * x) % 7 for x in range(7)] + [7])
_PSL27_S = tuple([7] + [(-pow(x, 5, 7)) % 7 for x in range(1, 7)] + [0])
_PERM_GENS = [
    [(1, 2, 0, 3, 4), (0, 1, 3, 4, 2)],        # A5 from two 3-cycles
    [(1, 0, 2, 3, 4), (1, 2, 3, 4, 0)],        # S5
    [_PSL27_T, _PSL27_M, _PSL27_S],            # PSL(2,7) on the projective line of 8 points
]

MAX_TABLE_INTS = 700_000
MAX_GROUPS = 40


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


def _perm_closure(gens, cap=400):
    """Return (order, table) of the permutation group generated by gens, or None if above cap."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems, index = [ident], {ident: 0}
    i = 0
    while i < len(elems):
        x = elems[i]
        i += 1
        for g in gens:
            y = tuple(g[t] for t in x)
            if y not in index:
                if len(elems) >= cap:
                    return None
                index[y] = len(elems)
                elems.append(y)
    table = [index[tuple(a[t] for t in b)] for a in elems for b in elems]
    return len(elems), table


def _group_specs(lo, hi):
    """Candidate groups with order in [lo, hi], split into affine, semidirect and permutation specs."""
    aff, sd, perm = [], [], []
    for q in range(2, hi + 1):
        if not lib.is_prime_power(q):
            continue
        for h in range(1, q):
            N = q * h
            if (q - 1) % h == 0 and lo <= N <= hi:
                aff.append((N, "aff", (q, h)))
    for N in range(max(lo, 1), hi + 1):
        for m in range(1, N + 1):
            if N % m:
                continue
            k = N // m
            for r in range(m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    sd.append((N, "sd", (m, k, r)))
    for gens in _PERM_GENS:
        cl = _perm_closure(gens)
        if cl is not None and lo <= cl[0] <= hi:
            perm.append((cl[0], "perm", cl[1]))
    return aff, sd, perm


def _affine_table(q, h, F):
    """Table of F_q x| H, H the subgroup of order h in F_q^*; element (a, j) is coded a*h + j."""
    b0 = F.pow(F.primitive_element(), (q - 1) // h)
    bj = np.array([F.pow(b0, j) for j in range(h)], dtype=np.int64)
    a = np.repeat(np.arange(q, dtype=np.int64), h)
    j = np.tile(np.arange(h, dtype=np.int64), q)
    # (a, j) * (c, l) = (a + b_j * c, j + l)
    prod = F.mul_table[bj[j][:, None], a[None, :]]
    new_a = F.add_table[a[:, None], prod]
    new_j = (j[:, None] + j[None, :]) % h
    return (new_a * h + new_j).ravel().tolist()


def _build_table(spec, gf_cache):
    N, kind, args = spec
    if kind == "perm":
        return args
    if kind == "aff":
        q, h = args
        if q not in gf_cache:
            gf_cache[q] = lib.GF(q)
        return _affine_table(q, h, gf_cache[q])
    m, k, r = args
    _, mul, _ = lib.semidirect_group(m, k, r)
    return [mul(x, y) for x in range(N) for y in range(N)]


def _pick_groups(lo, hi, seed):
    """Random sample of group tables, sized so the payload stays under MAX_TABLE_INTS."""
    aff, sd, perm = _group_specs(lo, hi)
    rng = random.Random(1000003 * int(seed) + 12345)
    rng.shuffle(aff)
    rng.shuffle(sd)
    pool = perm + aff[:16] + sd[:24]
    rng.shuffle(pool)
    gf_cache = {}
    out, used = [], 0
    for spec in pool:
        N = spec[0]
        if len(out) >= MAX_GROUPS or used + N * N > MAX_TABLE_INTS:
            continue
        out.append((N, _build_table(spec, gf_cache)))
        used += N * N
    return out


def _payload(groups, start):
    """Flat int list: groups, then the start graph as n, m and 2m endpoint ints."""
    p = [len(groups)]
    for N, tab in groups:
        p.append(N)
        p.extend(tab)
    n, edges = start
    p.extend([n, len(edges)])
    for u, v in edges:
        p.append(u)
        p.append(v)
    return p


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

    moore = lib.moore_bound(d, D)
    if best[0] >= moore or d > 32:
        return best

    # Groups that can beat the current graph with 1..4 base vertices per side.
    lo = max(2, (best[0] + 8) // 8, moore // 8)
    hi = moore // 2
    try:
        groups = _pick_groups(lo, hi, seed) if hi >= lo else []
        p = _payload(groups, best)
        if len(p) % 2:
            p.append(0)
        hdr = max(p) + 1
        pairs = list(zip(p[0::2], p[1::2]))

        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.5
        if budget < 2.0:
            return best
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=(hdr, pairs), timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError, MemoryError, OverflowError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
