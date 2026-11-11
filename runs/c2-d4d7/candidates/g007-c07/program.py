"""Non-metacyclic group lifts, then semidirect sweep, then grow-by-two repair.

Bold change in this version: the search space is widened from semidirect products Z_m x| Z_k
to arbitrary small permutation groups. Python supplies generators of products of alternating,
symmetric, dihedral, PSL(2,p), PGL(2,p) and cyclic groups (disjoint-block direct products).
The C engine closes each generator set into a full multiplication table (order <= 2048) and
hill-climbs Z-voltages with right multiplication on bi-regular bases with p = 1..4 fibres.
Left multiplication by the group is an automorphism, so the orbit-reduced BFS check still
applies. The phases are: permutation-group lifts (to 50% of the engine budget), the old
semidirect sweep (to 80%), then grow-by-two. Each candidate is checked by a full bitset
diameter test, and every output is checked with lib.is_valid. The H(3) incidence graph and
the W(q) start remain as fallbacks.
"""
import math
import time
import itertools

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (v2: permutation-group lifts).
 * Usage:   prog d D seed time_limit [specs]  < start_graph
 *   stdin:  "n m" then m lines "u v", or "0 0" for none.
 *   specs:  groups separated by ';'. Each group is "s:g1|g2|...", where each generator is
 *           s comma-separated images of 0..s-1 (a permutation). Empty string = no groups.
 *   stdout: "n m" then m lines "u v": the largest valid graph found.
 * Phase 1: voltage lifts over permutation groups (closed by the engine), fibres p = 1..4.
 * Phase 2: semidirect Z_m x| Z_k lift sweep.
 * Phase 3: grow-by-two annealing from the best graph found.
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
#define MAXG 2048
#define MAXS 32
#define MAXGEN 8
#define MAXSPEC 512
#define HSZ 8192
#define SWEEP_SPREAD 12

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

/* ---------- semidirect groups Z_m x|_r Z_k ---------- */
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

/* ---------- permutation groups given by generators ---------- */
typedef struct {
    int s, ng, order;
    unsigned char gen[MAXGEN][MAXS];
} Spec;

static Spec specs[MAXSPEC];
static int nspec = 0;

static unsigned char EL[MAXG][MAXS];   /* elements of the currently closed group; EL[0] = identity */
static int hidx[HSZ];
static uint16_t GT[MAXG * MAXG];        /* GT[x*N + y] = x*y, current group of order GN */
static int GN = 1;
static int cur_spec = -2;

static unsigned hash_perm(const unsigned char *p, int s) {
    uint32_t h = 2166136261u;
    for (int i = 0; i < s; i++) { h ^= p[i]; h *= 16777619u; }
    return h & (HSZ - 1);
}

/* Find p among EL[0..]; if absent and newidx >= 0, store newidx at the free slot. */
static int hlookup(const unsigned char *p, int s, int newidx) {
    unsigned h = hash_perm(p, s);
    for (;;) {
        int e = hidx[h];
        if (e < 0) {
            if (newidx >= 0) hidx[h] = newidx;
            return -1;
        }
        if (memcmp(EL[e], p, (size_t)s) == 0) return e;
        h = (h + 1) & (HSZ - 1);
    }
}

/* Close the generators under right multiplication from the identity. Returns order or 0. */
static int closure_only(const Spec *S) {
    int s = S->s, n = 1;
    unsigned char q[MAXS];
    memset(hidx, -1, sizeof hidx);
    for (int k = 0; k < s; k++) EL[0][k] = (unsigned char)k;
    hlookup(EL[0], s, 0);
    for (int i = 0; i < n; i++) {
        for (int g = 0; g < S->ng; g++) {
            for (int k = 0; k < s; k++) q[k] = EL[i][S->gen[g][k]];
            if (hlookup(q, s, -1) < 0) {
                if (n >= MAXG) return 0;
                memcpy(EL[n], q, (size_t)s);
                hlookup(q, s, n);
                n++;
            }
        }
    }
    return n;
}

/* Load spec si as the current group, building the full multiplication table. */
static int load_spec(int si) {
    if (cur_spec == si) return 1;
    cur_spec = -2;
    const Spec *S = &specs[si];
    int s = S->s;
    int n = closure_only(S);
    if (n <= 0) return 0;
    unsigned char q[MAXS];
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++) {
            for (int k = 0; k < s; k++) q[k] = EL[x][EL[y][k]];
            int z = hlookup(q, s, -1);
            if (z < 0) return 0;
            GT[x * n + y] = (uint16_t)z;
        }
    GN = n;
    cur_spec = si;
    return 1;
}

static void set_group_semidirect(const Grp *G) {
    int N = G->m * G->k;
    GN = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++) GT[x * N + y] = (uint16_t)gmul(G, x, y);
    cur_spec = -2;
}

/* Parse "s:g1|g2,...;s:..." into specs, keeping groups with 2d <= order <= MAXG. */
static void parse_specs(const char *str) {
    const char *p = str;
    nspec = 0;
    while (*p && nspec < MAXSPEC) {
        Spec S;
        char *end;
        int ok = 1;
        memset(&S, 0, sizeof S);
        long s = strtol(p, &end, 10);
        if (end == p || *end != ':' || s < 1 || s > MAXS) {
            ok = 0;
        } else {
            S.s = (int)s;
            p = end + 1;
            while (ok) {
                if (S.ng >= MAXGEN) { ok = 0; break; }
                int seen[MAXS];
                memset(seen, 0, sizeof seen);
                for (int k = 0; k < S.s; k++) {
                    long v = strtol(p, &end, 10);
                    if (end == p || v < 0 || v >= S.s || seen[v]) { ok = 0; break; }
                    seen[v] = 1;
                    S.gen[S.ng][k] = (unsigned char)v;
                    p = end;
                    if (k + 1 < S.s) {
                        if (*p != ',') { ok = 0; break; }
                        p++;
                    }
                }
                if (!ok) break;
                S.ng++;
                if (*p == '|') { p++; continue; }
                break;
            }
        }
        while (*p && *p != ';') p++;
        if (*p == ';') p++;
        if (ok && S.ng > 0) {
            int order = closure_only(&S);
            if (order >= 2 * d && order <= MAXG) {
                S.order = order;
                specs[nspec++] = S;
            }
        }
    }
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

/* Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i, j, g) joins A(i,x) to B(j, x*g). Left multiplication is an automorphism. */
static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= p * N); }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Orbit-reduced diameter objective: BFS from the identity of each fibre. Zero iff diam <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int nv = g->n;
    long total = 0;
    for (int b = 0; b < 2 * p; b++) {
        int src = b * GN;
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
static int lift_fast_try(Graph *g, int p, int N, int steps, double until) {
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
    build_lift(g, p, N, dt, nd);
    long bad = orbit_bad(g, p);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = orbit_bad(g, p);
        if (nb <= bad || rnd01() < 0.02) bad = nb;
        else dt[t].g = old;
    }
    build_lift(g, p, N, dt, nd);
    return bad == 0;
}

/* Phase 1: voltage lifts over permutation groups, fibres p = 1..MAXP. Keeps the smallest
 * window of lift sizes just above the current best. */
static void group_phase(Graph *best, double until) {
    static Graph cand;
    static int ps_[MAXSPEC * MAXP], pp_[MAXSPEC * MAXP];
    long moore = moore_bound();
    while (now() < until) {
        long minsz = -1;
        for (int si = 0; si < nspec; si++)
            for (int p = 1; p <= MAXP; p++) {
                long sz = 2L * p * specs[si].order;
                if (sz <= best->n || sz > moore || sz > MAXN) continue;
                if (minsz < 0 || sz < minsz) minsz = sz;
            }
        if (minsz < 0) return;
        long slack = 40 + best->n / 20;
        int cnt = 0;
        for (int si = 0; si < nspec; si++)
            for (int p = 1; p <= MAXP; p++) {
                long sz = 2L * p * specs[si].order;
                if (sz <= best->n || sz > moore || sz > MAXN) continue;
                if (sz <= minsz + slack) { ps_[cnt] = si; pp_[cnt] = p; cnt++; }
            }
        if (cnt == 0) return;
        int pick = rndint(cnt);
        if (!load_spec(ps_[pick])) { specs[ps_[pick]].order = 0; continue; }
        int p = pp_[pick];
        if (lift_fast_try(&cand, p, GN, 12000, until) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
    }
}

/* Phase 2: semidirect Z_m x| Z_k sweep, targeting sizes just above the best. */
static void lift_sweep(Graph *best, double until) {
    static Graph cand;
    static Grp G;
    long moore = moore_bound();
    while (now() < until) {
        int p = rndint(5) == 0 ? 2 : 1;
        int lo = best->n / (2 * p) + 1;
        int spread = SWEEP_SPREAD + best->n / 60;
        int N = lo + rndint(spread);
        if (N < 2 * d) N = 2 * d;
        if (2L * p * N > moore || 2 * p * N > MAXN) {
            N = lo < 2 * d ? 2 * d : lo;
            if (2L * p * N > moore || 2 * p * N > MAXN) {
                if (p == 1) return;
                continue;
            }
        }
        for (int a = 0; a < 4 && now() < until; a++) {
            if (!random_group(N, &G)) break;
            set_group_semidirect(&G);
            if (lift_fast_try(&cand, p, N, 12000, until) && cand.n > best->n && is_valid(&cand)) {
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
        fprintf(stderr, "usage: %s d D seed time_limit [specs] < start_graph\n", argv[0]);
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

    nspec = 0;
    if (argc > 5 && d >= 1 && d <= MAXD) parse_specs(argv[5]);

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) { complete_bipartite(&best); print_graph(&best); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        if (nspec > 0) group_phase(&best, t0 + (t_end - t0) * 0.5);
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


# ------------------------------------------------ permutation-group generators

def _primitive_root(p):
    for g in range(2, p):
        if len({pow(g, e, p) for e in range(1, p)}) == p - 1:
            return g
    return 1


def _perm_group(kind, k):
    """Return (order, degree, generator permutations as lists) for a small permutation group."""
    if kind == "cyc":
        return k, k, [[(i + 1) % k for i in range(k)]]
    if kind == "dih":
        return 2 * k, k, [[(i + 1) % k for i in range(k)], [(-i) % k for i in range(k)]]
    if kind == "sym":
        t = list(range(k))
        t[0], t[1] = 1, 0
        return math.factorial(k), k, [t, [(i + 1) % k for i in range(k)]]
    if kind == "alt":
        three = list(range(k))
        three[0], three[1], three[2] = 1, 2, 0
        if k % 2:
            c = [(i + 1) % k for i in range(k)]
        else:
            c = list(range(k))
            for i in range(1, k):
                c[i] = i + 1 if i + 1 < k else 1
        return math.factorial(k) // 2, k, [three, c]
    if kind in ("psl", "pgl"):
        p = k
        inf = p
        order = p * (p * p - 1) // (2 if kind == "psl" else 1)
        shift = [(t + 1) % p for t in range(p)] + [inf]
        inv = [inf if t == 0 else (-pow(t, p - 2, p)) % p for t in range(p)] + [0]
        gens = [shift, inv]
        if kind == "pgl":
            g = _primitive_root(p)
            gens.append([(g * t) % p for t in range(p)] + [inf])
        return order, p + 1, gens
    raise ValueError(kind)


_SINGLES = ([("cyc", k) for k in range(2, 33)]
            + [("dih", k) for k in range(3, 20)]
            + [("sym", 3), ("sym", 4), ("sym", 5), ("alt", 4), ("alt", 5),
               ("psl", 5), ("psl", 7), ("pgl", 5), ("pgl", 7), ("psl", 11)])


def _product_spec(d, parts):
    """Direct product of factors on disjoint point blocks: (order, spec text) or None."""
    facs = [_perm_group(kind, k) for kind, k in parts]
    order, total = 1, 0
    for o, deg, _ in facs:
        order *= o
        total += deg
    ngen = sum(len(g) for _, _, g in facs)
    if total > 32 or ngen > 8 or order < 2 * d or order > 1100:
        return None
    gens, off = [], 0
    for _, deg, gl in facs:
        for g in gl:
            ext = list(range(total))
            for i in range(deg):
                ext[off + i] = off + g[i]
            gens.append(ext)
        off += deg
    text = f"{total}:" + "|".join(",".join(map(str, g)) for g in gens)
    return order, text


def _group_specs(d, target=420, max_chars=60000):
    """Spec string for the C engine: groups whose orders are near target, sorted by closeness."""
    S = _SINGLES
    combos = [(a,) for a in S]
    combos += [(a, b) for i, a in enumerate(S) for b in S[i:]]
    items = []
    for parts in combos:
        r = _product_spec(d, parts)
        if r is None:
            continue
        order, text = r
        items.append((abs(math.log(order / target)), text))
    items.sort()
    out, chars = [], 0
    for _, text in items:
        if chars + len(text) + 1 > max_chars:
            continue
        out.append(text)
        chars += len(text) + 1
    return ";".join(out)


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
        specs = _group_specs(d)
    except Exception:
        specs = ""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget, specs],
                         stdin_graph=best, timeout=budget + 5)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
