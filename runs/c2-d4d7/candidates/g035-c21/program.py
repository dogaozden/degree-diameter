"""Bi-Cayley voltage-lift search with tabu search over voltages, for the weakest target (d=4, D=7).

Change from the parent: the random group-by-group simulated annealing is replaced by a systematic
search. Every lift candidate is a regular Z_m x|_r Z_k or (PSL/PGL)(2,p) x Z_k voltage lift over a
base multigraph on p <= 4 vertices per side. Candidate (group, p) pairs with lift order in a window
above the current best are sampled uniformly by reservoir sampling. Each candidate is attacked by
tabu search over single-voltage moves, scored by the orbit-reduced excess distance. The BFS runs
implicitly on the lift (no graph rebuild per move), and a full all-pairs check runs only on success.
Python builds the start graph (projective-plane, W(3), H(3) incidence), keeps a valid fallback, and
validates every C output with lib.is_valid before returning.
"""
import time

import itertools

import lib

C_SOURCE = r'''
/* Bi-Cayley / voltage-lift search with tabu search.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * A lift over a group G of order N with a p+p base multigraph (d-regular, parallel darts
 * allowed) has 2pN vertices: A-fibre i element x is vertex i*N+x, B-fibre j element y is
 * vertex p*N+j*N+y. Dart (i,j,g) joins A(i,x) to B(j, x*g). Left multiplication by G is an
 * automorphism, so distances from (a,x) equal distances from (a,e) to shifted targets, and it
 * suffices to BFS from the 2p fibre identities. Cost = sum over those BFS trees of max(0,dist-D),
 * with unreached vertices charged 2. Cost zero means diameter <= D.
 */
#define _POSIX_C_SOURCE 200809L
#include <limits.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 4096
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXP 4
#define MAXG 1400
#define HS 8192
#define NB 5
#define MAXCAND 4000
#define MAXDART (MAXD * MAXP)
#define TABU_SAMPLE 600
#define PERTURB_AFTER 250

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int i, j, g; } Dart;
typedef struct { int kind, b, m, k, r, N, p; } Cand;
typedef struct { int m, k, r; int rp[MAXG]; } Grp;
typedef struct { unsigned char p[16]; } Perm;

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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
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

static void add_edge(Graph *g, int u, int v) {
    g->adj[u][g->deg[u]++] = v;
    g->adj[v][g->deg[v]++] = u;
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

/* Number of unordered vertex pairs at distance > D, by bitset BFS. */
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

/* ---------------------------------------------------------------- base permutation groups */
static uint64_t hkey[HS];
static int hval[HS];
static Perm ELEM[MAXG];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (hval[h]) {
        if (hkey[h] == key) return hval[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (hval[h]) h = (h + 1) & (HS - 1);
    hkey[h] = key;
    hval[h] = idx + 1;
}

/* Closure of PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) acting on P^1(F_p) = {0..p-1, inf = p}. */
static int perm_closure(int p, int pgl, int *orderp) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) { prim = c; break; }
    }
    for (int x = 0; x <= p; x++)
        gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x + 1) % p);
    ng++;
    for (int x = 0; x <= p; x++) {
        int v;
        if (x == inf) v = 0;
        else if (x == 0) v = inf;
        else v = (int)((p - powmod(x, p - 2, p)) % p);
        gen[ng].p[x] = (unsigned char)v;
    }
    ng++;
    if (pgl) {
        for (int x = 0; x <= p; x++)
            gen[ng].p[x] = (unsigned char)((x == inf) ? inf : (x * prim) % p);
        ng++;
    }
    memset(hval, 0, sizeof hval);
    memset(&ELEM[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) ELEM[0].p[x] = (unsigned char)x;
    hput(pkey(ELEM[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= MAXG) return 0;
                ELEM[n] = h;
                hput(key, n);
                n++;
            }
        }
    }
    *orderp = n;
    return 1;
}

static int *make_base_table(int p, int pgl, int *ordp) {
    int ord = 0;
    if (!perm_closure(p, pgl, &ord)) return NULL;
    int s = p + 1;
    int *tab = malloc(sizeof(int) * (size_t)ord * (size_t)ord);
    if (!tab) return NULL;
    for (int i = 0; i < ord; i++)
        for (int j = 0; j < ord; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = ELEM[i].p[ELEM[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
        }
    *ordp = ord;
    return tab;
}

static int *base_tab[NB];
static int base_ord[NB];

static void init_bases(void) {
    static const int BP[NB] = {5, 5, 7, 7, 11};
    static const int BG[NB] = {0, 1, 0, 1, 0};
    for (int b = 0; b < NB; b++) {
        int ord = 0;
        base_tab[b] = make_base_table(BP[b], BG[b], &ord);
        base_ord[b] = base_tab[b] ? ord : 0;
    }
}

/* ---------------------------------------------------------------- current group */
static int GN;
static int GTAB[MAXG * MAXG];
static int INV[MAXG];
static Grp SG;

static int gmul(int x, int y) {
    int k = SG.k, m = SG.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)((a + (long)SG.rp[b] * c) % m) * k + (b + e) % k;
}

/* Install a candidate group into GTAB and INV. Returns 0 if the table is not a group. */
static int set_group(const Cand *c) {
    int N;
    if (c->kind == 0) {
        int m = c->m, k = c->k;
        N = m * k;
        SG.m = m;
        SG.k = k;
        SG.r = c->r;
        SG.rp[0] = 1 % m;
        for (int b = 1; b < k; b++) SG.rp[b] = (int)((long)SG.rp[b - 1] * c->r % m);
        GN = N;
        for (int x = 0; x < N; x++)
            for (int y = 0; y < N; y++)
                GTAB[x * N + y] = gmul(x, y);
    } else {
        int o = base_ord[c->b], k = c->k;
        N = o * k;
        GN = N;
        const int *bt = base_tab[c->b];
        if (!bt) return 0;
        for (int x = 0; x < o; x++)
            for (int cc = 0; cc < k; cc++)
                for (int y = 0; y < o; y++)
                    for (int e = 0; e < k; e++)
                        GTAB[(x * k + cc) * N + (y * k + e)] = bt[x * o + y] * k + (cc + e) % k;
    }
    for (int g = 0; g < N; g++) {
        int found = -1;
        for (int y = 0; y < N; y++)
            if (GTAB[g * N + y] == 0) { found = y; break; }
        if (found < 0) return 0;
        INV[g] = found;
    }
    return 1;
}

/* ---------------------------------------------------------------- candidate pool */
static Cand cands[MAXCAND];
static int ncands;
static long ntotal;

/* Reservoir sampling: keeps a uniform sample of all offered candidates. */
static void offer(Cand c) {
    ntotal++;
    if (ncands < MAXCAND) { cands[ncands++] = c; return; }
    uint64_t j = rnd() % (uint64_t)ntotal;
    if (j < MAXCAND) cands[j] = c;
}

/* All candidate groups with lift order 2pN in (best_n, hi]. */
static void enumerate_cands(long best_n, long hi) {
    ncands = 0;
    ntotal = 0;
    for (int p = 1; p <= MAXP; p++) {
        long Nlo = best_n / (2L * p) + 1;
        long Nhi = hi / (2L * p);
        if (Nlo < d) Nlo = d;
        if (Nlo < 2) Nlo = 2;
        if (Nhi > MAXG) Nhi = MAXG;
        for (long N = Nlo; N <= Nhi; N++) {
            int Ni = (int)N;
            for (int m = 1; m <= Ni; m++) {
                if (Ni % m) continue;
                int k = Ni / m;
                if (m == 1) {
                    Cand c = {0, 0, 1, k, 0, Ni, p};
                    offer(c);
                    continue;
                }
                for (int r = 1; r < m; r++) {
                    if (gcd(r, m) != 1) continue;
                    if (powmod(r, k, m) != 1 % m) continue;
                    Cand c = {0, 0, m, k, r, Ni, p};
                    offer(c);
                }
            }
            for (int b = 0; b < NB; b++) {
                if (base_ord[b] <= 0 || Ni % base_ord[b]) continue;
                Cand c = {1, b, 0, Ni / base_ord[b], 0, Ni, p};
                offer(c);
            }
        }
    }
}

/* ---------------------------------------------------------------- lift state and cost */
static Dart dt[MAXDART], bestdt[MAXDART];
static int nd;
static int rowd[MAXP][MAXD], rowcnt[MAXP];
static int cold[MAXP][MAXD], colcnt[MAXP];
static int tabu_until[MAXDART][MAXG];
static int dist_[MAXN], bq[MAXN];

/* Orbit-reduced excess distance on the implicit lift. */
static long excess_cost(int p) {
    int N = GN, half = p * N, nv = 2 * half;
    long total = 0;
    for (int s = 0; s < 2 * p; s++) {
        int src = s * N;
        for (int v = 0; v < nv; v++) dist_[v] = -1;
        int head = 0, tail = 0;
        dist_[src] = 0;
        bq[tail++] = src;
        while (head < tail) {
            int v = bq[head++];
            int dv = dist_[v] + 1;
            if (v < half) {
                int i = v / N, x = v - i * N;
                for (int k = 0; k < rowcnt[i]; k++) {
                    const Dart *e = &dt[rowd[i][k]];
                    int u = half + e->j * N + GTAB[x * N + e->g];
                    if (dist_[u] < 0) { dist_[u] = dv; bq[tail++] = u; }
                }
            } else {
                int w = v - half;
                int j = w / N, y = w - j * N;
                for (int k = 0; k < colcnt[j]; k++) {
                    const Dart *e = &dt[cold[j][k]];
                    int u = e->i * N + GTAB[y * N + INV[e->g]];
                    if (dist_[u] < 0) { dist_[u] = dv; bq[tail++] = u; }
                }
            }
        }
        for (int v = 0; v < nv; v++) {
            if (dist_[v] < 0) total += 2;
            else if (dist_[v] > D) total += dist_[v] - D;
        }
    }
    return total;
}

/* Random d-regular bipartite base multigraph on p + p vertices, connected. */
static void make_base(int p, int M[MAXP][MAXP]) {
    for (;;) {
        memset(M, 0, sizeof(int) * MAXP * MAXP);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
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

static void setup_darts(int p) {
    int M[MAXP][MAXP];
    make_base(p, M);
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = -1;
                nd++;
            }
    for (int i = 0; i < p; i++) { rowcnt[i] = 0; colcnt[i] = 0; }
    for (int t = 0; t < nd; t++) {
        rowd[dt[t].i][rowcnt[dt[t].i]++] = t;
        cold[dt[t].j][colcnt[dt[t].j]++] = t;
    }
}

/* A voltage is free if no other dart on the same (i,j) pair uses it (avoids parallel edges). */
static int voltage_free(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && dt[s].g == g && dt[s].i == dt[t].i && dt[s].j == dt[t].j) return 0;
    return 1;
}

static int fresh_voltage(int t) {
    int g = rndint(GN), guard = 0;
    while (!voltage_free(t, g) && guard++ < 100000) g = rndint(GN);
    return g;
}

static void build_explicit(Graph *g, int p) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GTAB[x * N + dt[t].g]);
}

/* Tabu search over single-voltage moves for the current group and base size p. */
static int tabu_lift(int p, double until, Graph *out) {
    int N = GN;
    if (N < 2) return 0;
    setup_darts(p);
    for (int t = 0; t < nd; t++) dt[t].g = fresh_voltage(t);
    for (int t = 0; t < nd; t++) memset(tabu_until[t], 0, sizeof(int) * N);
    long cur = excess_cost(p);
    long best = cur;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    int total_moves = nd * (N - 1);
    int sample = total_moves > TABU_SAMPLE;
    int reps = sample ? TABU_SAMPLE : total_moves;
    long step = 0;
    int since = 0;
    while (best > 0 && now() < until) {
        step++;
        long bmove = LONG_MAX;
        int bt = -1, bg = -1, nties = 0;
        for (int it = 0; it < reps; it++) {
            int t, g;
            if (sample) {
                t = rndint(nd);
                g = rndint(N);
                if (g == dt[t].g) continue;
            } else {
                t = it / (N - 1);
                int k = it - t * (N - 1);
                g = (k >= dt[t].g) ? k + 1 : k;
            }
            int old = dt[t].g;
            if (!voltage_free(t, g)) continue;
            dt[t].g = g;
            long c = excess_cost(p);
            dt[t].g = old;
            if (tabu_until[t][g] > step && c >= best) continue;
            if (c < bmove) {
                bmove = c;
                bt = t;
                bg = g;
                nties = 1;
            } else if (c == bmove && rndint(++nties) == 0) {
                bt = t;
                bg = g;
            }
        }
        int kick = (bt < 0);
        if (!kick) {
            int old = dt[bt].g;
            tabu_until[bt][old] = (int)step + 6 + rndint(10);
            dt[bt].g = bg;
            cur = bmove;
            if (cur < best) {
                best = cur;
                memcpy(bestdt, dt, sizeof(Dart) * nd);
                since = 0;
            } else {
                since++;
            }
        }
        if (kick || since > PERTURB_AFTER) {
            memcpy(dt, bestdt, sizeof(Dart) * nd);
            int kicks = 2 + rndint(2);
            for (int k = 0; k < kicks; k++) {
                int t = rndint(nd);
                dt[t].g = fresh_voltage(t);
            }
            cur = excess_cost(p);
            since = 0;
            for (int t = 0; t < nd; t++) memset(tabu_until[t], 0, sizeof(int) * N);
        }
    }
    if (best > 0) return 0;
    memcpy(dt, bestdt, sizeof(Dart) * nd);
    build_explicit(out, p);
    return is_valid(out);
}

/* Repeatedly sample a candidate group and run tabu on it, until time runs out. */
static void lift_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    while (now() < until) {
        long hi = best->n + best->n / 4 + 60;
        if (hi > moore) hi = moore;
        if (hi > MAXN) hi = MAXN;
        if (hi <= best->n) return;
        enumerate_cands(best->n, hi);
        if (ncands == 0) return;
        Cand cd = cands[rndint(ncands)];
        double slice = (until - now()) / 4.0;
        if (slice < 2.0) slice = 2.0;
        if (slice > 8.0) slice = 8.0;
        double stop = now() + slice;
        if (stop > until) stop = until;
        if (!set_group(&cd)) continue;
        if (tabu_lift(cd.p, stop, &cand) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
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
    t_end = t0 + limit * 0.92;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (D >= 2 && best.n > 0 && best.n < moore_bound()) {
        init_bases();
        lift_search(&best, t_end);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention yields a graph that passes lib.is_valid with diameter 6.
    """
    q = 3

    def norm(v):
        c = next(x for x in v if x)
        inv = 1 if c == 1 else 2
        return tuple((x * inv) % q for x in v)

    vecs = itertools.product(range(q), repeat=7)
    pts = sorted({norm(v) for v in vecs if any(v) and
                  (v[0] * v[4] + v[1] * v[5] + v[2] * v[6] - v[3] * v[3]) % q == 0})
    P = len(pts)
    index = {p: i for i, p in enumerate(pts)}

    def bil(x, y):
        return (x[0] * y[4] + x[4] * y[0] + x[1] * y[5] + x[5] * y[1] +
                x[2] * y[6] + x[6] * y[2] + x[3] * y[3]) % q

    def pl(x, y, i, j):
        return (x[i] * y[j] - x[j] * y[i]) % q

    conds = [((1, 2), (3, 4)), ((5, 4), (3, 2)), ((2, 0), (3, 5)),
             ((6, 5), (3, 0)), ((0, 1), (3, 6)), ((4, 6), (3, 1))]
    combos = ((1, 0), (0, 1), (1, 1), (1, 2))
    for s in (1, -1):
        lines = set()
        for i in range(P):
            x = pts[i]
            for j in range(i + 1, P):
                y = pts[j]
                if bil(x, y):
                    continue
                if any((pl(x, y, *a) - s * pl(x, y, *b)) % q for a, b in conds):
                    continue
                L = frozenset(index[norm(tuple((a * x[k] + b * y[k]) % q for k in range(7)))]
                              for a, b in combos)
                lines.add(L)
        if len(lines) != P or any(len(L) != 4 for L in lines):
            continue
        ordered = sorted(lines, key=sorted)
        edges = [(p, P + j) for j, L in enumerate(ordered) for p in L]
        n = P + len(ordered)
        if lib.is_valid(n, edges, 4, 6):
            return n, edges
    return None


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidate graphs valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    if d == 4 and D >= 6:
        try:
            gh = _gh_h3()
        except Exception:
            gh = None
        if gh is not None:
            out.append(gh)
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 0.2:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 6)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
