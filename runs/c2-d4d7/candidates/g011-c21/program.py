"""Non-metacyclic group-lift search (bold variant) with grow-by-two repair.

Change from the parent: the bi-Cayley sweep now also draws voltages over permutation
groups built from generators (direct products of A4, S4, A5, S5, PSL(2,7), dihedral and
cyclic groups). These groups are not metacyclic, so they reach orders the Z_m x| Z_k
family does not. A5 x Z_7 has order 420, which gives an 840-vertex Haar-type lift.
The C engine builds each group's multiplication table by closure. Metacyclic groups stay
in the same sweep as a fallback. The H(3) incidence graph (or K_{d,d}) is the start and
the safe fallback. Every output is checked with lib.is_valid before it is accepted.
"""
import itertools
import random
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (bi-Cayley lifts over arbitrary groups).
 * Usage:   prog d D seed time_limit [groups]  < start_graph
 *   stdin:  "n m" then m lines "u v", or "0 0" for none.
 *   groups: optional, '|'-separated permutation groups "deg:g1;g2;..." where each
 *           generator is deg comma-separated images (0-indexed).
 *   stdout: "n m" then m lines "u v": the largest valid graph found.
 * Phase 1: bi-Cayley lift sweep; voltages over the given permutation groups or over
 *          random semidirect groups Z_m x| Z_k.
 * Phase 2: grow-by-two annealing from the best graph found.
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
#define SWEEP_SPREAD 12
#define GMAX 2048
#define MAXPERM 32
#define MAXGROUPS 64
#define MAXGEN 8
#define HSIZE 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

/* A finite group as a multiplication table: T[x*N+y] = x*y, identity index 0. */
typedef struct {
    int N;
    uint16_t *T;
} Group;

typedef struct {
    int m, k, r;
    int rp[MAXN];
} Grp;

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

/* ---------- metacyclic groups Z_m x|_r Z_k: element a*k + b ---------- */

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

/* ---------- permutation groups given by generators (closure in C) ---------- */

static unsigned char EL[GMAX][MAXPERM];
static int HT[HSIZE];

static unsigned hperm(const unsigned char *p, int deg) {
    unsigned h = 2166136261u;
    for (int i = 0; i < deg; i++) { h ^= p[i]; h *= 16777619u; }
    return h;
}

static int perm_find(const unsigned char *p, int deg) {
    unsigned h = hperm(p, deg) & (HSIZE - 1);
    for (;;) {
        int e = HT[h];
        if (!e) return -1;
        if (memcmp(EL[e - 1], p, (size_t)deg) == 0) return e - 1;
        h = (h + 1) & (HSIZE - 1);
    }
}

/* Returns the index of p, inserting it if new. Returns -1 if the group exceeds GMAX. */
static int perm_insert(const unsigned char *p, int deg, int *N) {
    int f = perm_find(p, deg);
    if (f >= 0) return f;
    if (*N >= GMAX) return -1;
    memcpy(EL[*N], p, (size_t)deg);
    unsigned h = hperm(p, deg) & (HSIZE - 1);
    while (HT[h]) h = (h + 1) & (HSIZE - 1);
    HT[h] = *N + 1;
    return (*N)++;
}

/* Parse "deg:g1;g2;..." and build the table of the generated group. Returns 1 on success. */
static int build_perm_group(const char *s, Group *G) {
    char *end = NULL;
    long deg = strtol(s, &end, 10);
    if (end == s || *end != ':' || deg < 1 || deg > MAXPERM) return 0;
    static int gens[MAXGEN][MAXPERM];
    int ng = 0;
    const char *c = end + 1;
    while (*c) {
        if (ng >= MAXGEN) return 0;
        for (int i = 0; i < deg; i++) {
            long v = strtol(c, &end, 10);
            if (end == c || v < 0 || v >= deg) return 0;
            gens[ng][i] = (int)v;
            c = end;
            if (i + 1 < deg) {
                if (*c != ',') return 0;
                c++;
            }
        }
        unsigned char seen[MAXPERM];
        memset(seen, 0, sizeof seen);
        for (int i = 0; i < deg; i++) {
            if (seen[gens[ng][i]]) return 0;
            seen[gens[ng][i]] = 1;
        }
        ng++;
        if (*c == ';') c++;
        else if (*c != '\0') return 0;
    }
    memset(HT, 0, sizeof HT);
    int N = 0;
    int dg = (int)deg;
    unsigned char p[MAXPERM], r[MAXPERM];
    memset(p, 0, sizeof p);
    for (int i = 0; i < dg; i++) p[i] = (unsigned char)i;
    if (perm_insert(p, dg, &N) < 0) return 0;
    for (int q = 0; q < N; q++)
        for (int s2 = 0; s2 < ng; s2++) {
            for (int i = 0; i < dg; i++) r[i] = EL[q][gens[s2][i]];
            if (perm_insert(r, dg, &N) < 0) return 0;
        }
    G->N = N;
    G->T = malloc(sizeof(uint16_t) * (size_t)N * (size_t)N);
    if (!G->T) return 0;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) {
            for (int i = 0; i < dg; i++) r[i] = EL[x][EL[y][i]];  /* x o y */
            int z = perm_find(r, dg);
            if (z < 0) { free(G->T); G->T = NULL; return 0; }
            G->T[(size_t)x * N + y] = (uint16_t)z;
        }
    return 1;
}

static Group pgroups[MAXGROUPS];
static int npgroups = 0;

static void parse_groups(const char *spec) {
    npgroups = 0;
    if (!spec || !*spec) return;
    size_t L = strlen(spec);
    char *buf = malloc(L + 1);
    if (!buf) return;
    memcpy(buf, spec, L + 1);
    char *tok = buf;
    while (tok && npgroups < MAXGROUPS) {
        char *bar = strchr(tok, '|');
        if (bar) *bar = '\0';
        Group G;
        G.N = 0;
        G.T = NULL;
        if (build_perm_group(tok, &G) && G.N >= 2) pgroups[npgroups++] = G;
        else if (G.T) free(G.T);
        if (!bar) break;
        tok = bar + 1;
    }
    free(buf);
}

/* Metacyclic table storage, reused across attempts. */
static uint16_t METAT[GMAX * GMAX];
static Grp MG;
static Group MGROUP;

/* Choose a group of order N: a permutation group with probability 0.8 when one exists,
 * otherwise a random semidirect group of that order. */
static const Group *pick_group(int N) {
    int cand[MAXGROUPS], nc = 0;
    for (int i = 0; i < npgroups; i++)
        if (pgroups[i].N == N) cand[nc++] = i;
    if (nc && rnd01() < 0.8) return &pgroups[cand[rndint(nc)]];
    if (!random_group(N, &MG)) return NULL;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            METAT[(size_t)x * N + y] = (uint16_t)gmul(&MG, x, y);
    MGROUP.N = N;
    MGROUP.T = METAT;
    return &MGROUP;
}

/* ---------- lifts ---------- */

typedef struct { int i, j, g; } Dart;

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element y -> (p+j)*N + y.
 * Dart (i, j, g) joins A(i,x) to B(j, x*g). */
static void build_lift(Graph *g, int p, int N, const Group *G, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x,
                     p * N + dt[t].j * N + G->T[(size_t)x * N + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective. Left multiplication is an automorphism of every lift,
 * so BFS from the identity of each fibre suffices. Zero iff diameter <= D. */
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
static int lift_fast_try(Graph *g, int p, int N, const Group *G, int steps, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
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

/* Sweep: pick a group order N just above the current best lift, and a group of that order
 * (a permutation group if one exists, else metacyclic). Keep any valid larger lift. */
static void lift_sweep(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        int p = rndint(5) == 0 ? 2 : 1;
        int lo = best->n / (2 * p) + 1;
        int spread = SWEEP_SPREAD + best->n / 60;
        int N = lo + rndint(spread);
        if (npgroups && rnd01() < 0.6) {
            int pool[MAXGROUPS], np = 0;
            for (int i = 0; i < npgroups; i++)
                if (pgroups[i].N >= lo && pgroups[i].N < lo + spread) pool[np++] = i;
            if (np) N = pgroups[pool[rndint(np)]].N;
        }
        if (2L * p * N > moore || 2 * p * N > MAXN) {
            N = lo;
            if (2L * p * N > moore || 2 * p * N > MAXN) {
                if (p == 1) return;
                continue;
            }
        }
        for (int a = 0; a < 4 && now() < until; a++) {
            const Group *G = pick_group(N);
            if (!G) break;
            if (lift_fast_try(&cand, p, N, G, 12000, until) && cand.n > best->n &&
                is_valid(&cand)) {
                copy_graph(best, &cand);
                break;
            }
        }
    }
}

/* ---------- grow-by-two repair ---------- */

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

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit [groups] < start_graph\n", argv[0]);
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

    MGROUP.T = METAT;
    parse_groups(argc >= 6 ? argv[5] : "");

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        lift_sweep(&best, t0 + (t_end - t0) * 0.8);
        if (best.n > 0) grow_search(&best, t_end);
    }
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


def _h3_lines(pts, index, s):
    """Lines of H(3) from Tits' description, with the right-hand sign multiplier s (1 or 2 mod 3)."""
    P = len(pts)

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1]
                + x[2] * y[6] + x[6] * y[2] - 2 * x[3] * y[3]) % 3

    def norm(v):
        c = next(t for t in v if t)
        inv = 1 if c == 1 else 2
        return tuple((t * inv) % 3 for t in v)

    lines = set()
    for i in range(P):
        x = pts[i]
        for j in range(i + 1, P):
            y = pts[j]
            if bil(x, y):
                continue

            def pl(a, b):
                return (x[a] * y[b] - x[b] * y[a]) % 3

            conds = [(pl(1, 2), pl(3, 4)), (pl(5, 4), pl(3, 2)), (pl(2, 0), pl(3, 5)),
                     (pl(6, 5), pl(3, 0)), (pl(0, 1), pl(3, 6)), (pl(4, 6), pl(3, 1))]
            if any((a - s * b) % 3 for a, b in conds):
                continue
            L = set()
            for a in range(3):
                for b in range(3):
                    if a == 0 and b == 0:
                        continue
                    v = tuple((a * x[k] + b * y[k]) % 3 for k in range(7))
                    if any(v):
                        L.add(index[norm(v)])
            if len(L) == 4:
                lines.add(tuple(sorted(L)))
    return lines


def _hexagon_h3():
    """Incidence graph of the split Cayley hexagon H(3): 728 vertices, 4-regular, diameter 6.

    Both sign conventions are tried, and the result is accepted only if lib.is_valid confirms
    it. Returns (n, edges) or None.
    """
    pts = []
    for v in itertools.product(range(3), repeat=7):
        if not any(v):
            continue
        if v[next(i for i, c in enumerate(v) if c)] != 1:
            continue
        if (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % 3:
            continue
        pts.append(v)
    P = len(pts)
    if P != 364:
        return None
    index = {v: i for i, v in enumerate(pts)}
    for s in (1, 2):
        lines = _h3_lines(pts, index, s)
        if len(lines) != P:
            continue
        lines = sorted(lines)
        edges = [(p, P + j) for j, L in enumerate(lines) for p in L]
        if lib.is_valid(2 * P, edges, 4, 6):
            return 2 * P, edges
    return None


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


# ---------------------------------------------------------------- permutation groups

_FACTORS = None
_NONABELIAN = {"A4", "S4", "A5", "S5", "PSL27"}
_GROUP_CAP = 48


def _closure_size(deg, gens, cap):
    """Order of the group generated by the permutations gens (tuples of length deg), or None if > cap."""
    ident = tuple(range(deg))
    seen = {ident}
    frontier = [ident]
    while frontier:
        nxt = []
        for e in frontier:
            for s in gens:
                pr = tuple(e[s[i]] for i in range(deg))
                if pr not in seen:
                    if len(seen) >= cap:
                        return None
                    seen.add(pr)
                    nxt.append(pr)
        frontier = nxt
    return len(seen)


def _cycle(deg, *cycles):
    """Permutation of range(deg) with the given cycles (each a tuple of points)."""
    p = list(range(deg))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def _psl27_gens():
    """Two permutations of 7 points generating the 168-element automorphism group of the Fano plane."""
    lines = [frozenset((x + a) % 7 for a in (0, 1, 3)) for x in range(7)]
    lineset = set(lines)
    auts = []
    for perm in itertools.permutations(range(7)):
        if all(frozenset(perm[p] for p in L) in lineset for L in lines):
            auts.append(perm)
    if len(auts) != 168:
        return None
    rng = random.Random(7)
    for _ in range(400):
        g, h = rng.sample(auts, 2)
        if _closure_size(7, [g, h], 200) == 168:
            return [g, h]
    return None


def _factors():
    """Small permutation groups (name, order, degree, generators), each verified by closure."""
    global _FACTORS
    if _FACTORS is not None:
        return _FACTORS
    fs = []

    def add(name, deg, gens, order):
        if _closure_size(deg, gens, 2 * order + 2) == order:
            fs.append((name, order, deg, tuple(gens)))

    for k in range(2, 13):
        add(f"Z{k}", k, [_cycle(k, tuple(range(k)))], k)
    for m in range(3, 13):
        add(f"D{m}", m, [_cycle(m, tuple(range(m))), tuple((-i) % m for i in range(m))], 2 * m)
    add("A4", 4, [_cycle(4, (0, 1, 2)), _cycle(4, (1, 2, 3))], 12)
    add("S4", 4, [_cycle(4, (0, 1, 2, 3)), _cycle(4, (0, 1))], 24)
    add("A5", 5, [_cycle(5, (0, 1, 2)), _cycle(5, (0, 1, 2, 3, 4))], 60)
    add("S5", 5, [_cycle(5, (0, 1, 2, 3, 4)), _cycle(5, (0, 1))], 120)
    psl = _psl27_gens()
    if psl is not None:
        fs.append(("PSL27", 168, 7, tuple(psl)))
    _FACTORS = fs
    return fs


def _is_nonabelian(name):
    return name in _NONABELIAN or name.startswith("D")


def _product_specs(lo, hi):
    """Direct products (disjoint supports) of up to three factors, with a non-abelian factor and
    order in [lo, hi]. Returns a list of (order, spec) with spec = "deg:g1;g2;..."."""
    fs = _factors()
    out = {}
    for r in (1, 2, 3):
        for combo in itertools.combinations_with_replacement(range(len(fs)), r):
            order = 1
            deg = 0
            for i in combo:
                order *= fs[i][1]
                deg += fs[i][2]
            if not lo <= order <= hi or deg > 32:
                continue
            if not any(_is_nonabelian(fs[i][0]) for i in combo):
                continue
            gens = []
            off = 0
            for i in combo:
                _, _, dg, gs = fs[i]
                for g in gs:
                    full = list(range(deg))
                    for k in range(dg):
                        full[off + k] = off + g[k]
                    gens.append(full)
                off += dg
            if len(gens) > 8:
                continue
            spec = f"{deg}:" + ";".join(",".join(str(x) for x in g) for g in gens)
            out[(order, spec)] = True
    return list(out.keys())


def _group_spec(best_n, seed):
    """Groups for the C sweep. Orders just above best_n/2 (the d-regular 1-fibre lifts) come first."""
    lo = max(2, best_n // 4)
    hi = best_n // 2 + 150
    t_lo = best_n // 2 + 1
    t_hi = t_lo + 80
    cands = _product_specs(lo, hi)
    rng = random.Random(1000003 * (seed + 1) + best_n)
    inner = [c for c in cands if t_lo <= c[0] <= t_hi]
    outer = [c for c in cands if not (t_lo <= c[0] <= t_hi)]
    rng.shuffle(inner)
    rng.shuffle(outer)
    chosen = (inner + outer)[:_GROUP_CAP]
    return "|".join(spec for _, spec in chosen)


# ---------------------------------------------------------------- build

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

    if d == 4 and D >= 6:
        try:
            hexg = _hexagon_h3()
        except Exception:
            hexg = None
        if hexg is not None and hexg[0] > best[0] and lib.is_valid(hexg[0], hexg[1], d, D):
            best = hexg

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
    if budget <= 0.2:
        return best
    try:
        spec = _group_spec(best[0], seed)
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, spec],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
