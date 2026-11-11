"""Bi-Cayley-style voltage lifts over non-metacyclic groups, with an orbit-reduced annealing search.

Changes from the parent (bold, high-risk):
  * Lift search is now simulated annealing over voltages (not iterated hill-climbing with restarts).
    The objective counts unreached (fibre representative, vertex) pairs, using BFS from the 2p fibre
    identities only. This is exact for regular left-multiplication actions.
  * Group families are PSL(2,p)/PGL(2,p) for p in {5,7,11}, each times Z_k, plus semidirect
    Z_m x|_r Z_k. Target orders are a window just above the current best, with a width that grows
    with the order, so non-metacyclic groups actually fit the window.
  * Lift phase gets the first half of the engine window; grow-by-two gets the rest.
  * Every output is re-checked by the full bitset all-pairs test in C and by lib.is_valid in Python.
    If anything fails, the best valid graph seen so far (ultimately K_{d,d} or a known start) is returned.
"""
import itertools
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
#define MAXW (MAXN / 64)
#define MAXD 8
#define MAXG 1024
#define MAXP 2
#define HS 4096

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int type, base, k, m, r, N; } GDesc;
typedef struct { int i, j, g; } Dart;
typedef struct { unsigned char p[16]; } Perm;

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

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

static int moore_bound_c(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2 * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return (int)(2 * s);
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

/* Number of unordered pairs at distance > D, by bitset BFS. */
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

static int read_start(Graph *g) {
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return 0;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return 0;
        }
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
                else if (g->side[u] == g->side[v]) { g->n = 0; return 0; }
            }
        }
    }
    if (!is_valid(g)) { g->n = 0; return 0; }
    return 1;
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

/* ---------------------------------------------------------------- groups
 * GT[x*GN+y] is the product x*y, identity 0. All groups act regularly on themselves by left
 * multiplication, which is what the orbit-reduced check needs. */
static int GN;
static int GT[MAXG * MAXG];
static int BT[MAXG * MAXG];
static int rp[MAXG];
static int cur_base = -1, cur_o = 0;
static const int BP[5] = {5, 5, 7, 7, 11};
static const int BG[5] = {0, 1, 0, 1, 0};

static Perm EL[MAXG];
static uint64_t hk[HS];
static int hv[HS];

static uint64_t pkey(const unsigned char *p, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)p[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t k) { return (unsigned)((k * 0x9E3779B97F4A7C15ULL) >> 52); }

static void hclear(void) { memset(hv, 0, sizeof hv); }

static int hget(uint64_t k) {
    unsigned h = hslot(k);
    while (hv[h]) {
        if (hk[h] == k) return hv[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hset(uint64_t k, int idx) {
    unsigned h = hslot(k);
    while (hv[h]) h = (h + 1) & (HS - 1);
    hk[h] = k;
    hv[h] = idx + 1;
}

/* Closure of PSL(2,p) (pgl=0) or PGL(2,p) (pgl=1) on the p+1 points of P^1. Returns order or 0. */
static int perm_group(int p, int pgl) {
    int s = p + 1, inf = p, ng = 0, prim = 1;
    Perm gen[3];
    memset(gen, 0, sizeof gen);
    for (int c = 2; c < p && prim == 1; c++) {
        int ok = 1;
        for (int e = 1; e < p - 1 && ok; e++)
            if (powmod(c, e, p) == 1) ok = 0;
        if (ok) prim = c;
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
    hclear();
    memset(&EL[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) EL[0].p[x] = (unsigned char)x;
    hset(pkey(EL[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hget(key) < 0) {
                if (n >= MAXG) return 0;
                EL[n] = h;
                hset(key, n);
                n++;
            }
        }
    }
    return n;
}

/* Multiplication table of base group b (index b-th entry of BP/BG) into BT. */
static int build_base(int b) {
    int o = perm_group(BP[b], BG[b]);
    if (o <= 0) return 0;
    int s = BP[b] + 1;
    for (int i = 0; i < o; i++)
        for (int j = 0; j < o; j++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = EL[i].p[EL[j].p[x]];
            int idx = hget(pkey(h.p, s));
            BT[i * o + j] = idx < 0 ? 0 : idx;
        }
    cur_base = b;
    cur_o = o;
    return o;
}

static int ensure_base(int b) {
    if (cur_base != b) {
        if (!build_base(b)) return 0;
    }
    return cur_o;
}

/* Install group G in GT. */
static void set_group(const GDesc *G) {
    if (G->type == 1) {
        ensure_base(G->base);
        int o = cur_o, k = G->k, N = o * k;
        GN = N;
        for (int x = 0; x < o; x++)
            for (int c = 0; c < k; c++)
                for (int y = 0; y < o; y++)
                    for (int e = 0; e < k; e++)
                        GT[(x * k + c) * N + (y * k + e)] = BT[x * o + y] * k + (c + e) % k;
    } else {
        int m = G->m, k = G->k, N = m * k;
        GN = N;
        rp[0] = 1 % m;
        for (int b = 1; b < k; b++) rp[b] = (int)((long)rp[b - 1] * G->r % m);
        for (int x = 0; x < N; x++) {
            int a = x / k, b = x % k;
            for (int y = 0; y < N; y++) {
                int c = y / k, e = y % k;
                GT[x * N + y] = (int)(((a + (long)rp[b] * c) % m) * k + (b + e) % k);
            }
        }
    }
}

/* Choose a group of order in [lo, hi]: PSL/PGL(2,p) x Z_k, or Z_m x|_r Z_k. */
static int pick_group(int lo, int hi, GDesc *G) {
    if (rndint(10) < 6) {
        int b = rndint(5);
        int o = ensure_base(b);
        if (o <= 0 || o > hi) return 0;
        int kl = (lo + o - 1) / o;
        if (kl < 1) kl = 1;
        int kh = hi / o;
        if (kl > kh) return 0;
        G->type = 1;
        G->base = b;
        G->k = kl + rndint(kh - kl + 1);
        G->m = 0;
        G->r = 0;
        G->N = o * G->k;
        return 1;
    }
    int N = lo + rndint(hi - lo + 1);
    for (int tries = 0; tries < 40; tries++) {
        int m = 1 + rndint(N);
        if (N % m) continue;
        int k = N / m;
        if (m == 1) break;
        int r = 1 + rndint(m - 1);
        if (gcd(r, m) != 1 || powmod(r, k, m) != 1 % m) continue;
        G->type = 0; G->m = m; G->k = k; G->r = r; G->N = N;
        return 1;
    }
    G->type = 0; G->m = 1; G->k = N; G->r = 0; G->N = N;
    return 1;
}

/* ---------------------------------------------------------------- voltage lifts
 * Vertex layout: A-fibre i, element x -> i*N + x; B-fibre j, element x -> (p+j)*N + x.
 * Dart (i,j,g) joins A(i,x) to B(j, x*g) for all x. */
static Dart bestdt[MAXP * MAXD];
static Graph tmpg;

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
        int seen[2 * MAXP] = {0}, st[2 * MAXP], top = 0, ns = 1;
        seen[0] = 1;
        st[top++] = 0;
        while (top) {
            int v = st[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && M[v][u - p] > 0) : (u < p && M[u][v - p] > 0);
                if (linked) { seen[u] = 1; ns++; st[top++] = u; }
            }
        }
        if (ns == 2 * p) return;
    }
}

static int fresh_volt(const Dart *dt, int nd, int skip, int i, int j) {
    for (;;) {
        int g = rndint(GN), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

static void build_lift(Graph *g, int p, const Dart *dt, int nd) {
    int N = GN;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = (unsigned char)(v >= p * N); }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + GT[x * N + dt[t].g]);
}

/* Unreached (fibre identity, vertex) pairs over the 2p fibre identities. Zero iff diameter <= D. */
static int dist_buf[MAXN], queue_buf[MAXN];

static long orbit_bad(const Graph *g, int p) {
    int N = GN, nv = g->n;
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

/* Simulated annealing over the voltages of one random base multigraph on p+p vertices. */
static int anneal_lift(Graph *out, int p, double until) {
    int M[MAXP][MAXP];
    Dart dt[MAXP * MAXD];
    int nd = 0;
    if (GN < d) return 0;
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = 0;
                nd++;
            }
    for (int t = 0; t < nd; t++) dt[t].g = fresh_volt(dt, nd, t, dt[t].i, dt[t].j);
    build_lift(&tmpg, p, dt, nd);
    long bad = orbit_bad(&tmpg, p);
    long bestbad = bad;
    memcpy(bestdt, dt, sizeof(Dart) * nd);
    double T = 1.0;
    long it = 0;
    while (bestbad > 0) {
        if ((++it & 31) == 0 && now() > until) break;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_volt(dt, nd, t, dt[t].i, dt[t].j);
        build_lift(&tmpg, p, dt, nd);
        long nb = orbit_bad(&tmpg, p);
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
        else dt[t].g = old;
        if (bad < bestbad) {
            bestbad = bad;
            memcpy(bestdt, dt, sizeof(Dart) * nd);
        }
        T *= 0.9995;
        if (T < 0.05) T = 1.0;
    }
    if (bestbad != 0) return 0;
    build_lift(out, p, bestdt, nd);
    return is_valid(out);
}

/* Look for lifts strictly larger than the current best, group by group, until the deadline. */
static void lift_phase(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound_c();
    while (now() < until) {
        int p = 1 + rndint(MAXP);
        long target = best->n + 2;
        long lo = (target + 2 * p - 1) / (2 * p);
        long hi = lo + (lo / 6 > 8 ? lo / 6 : 8);
        if (hi > MAXG) hi = MAXG;
        if (lo > hi || 2L * p * lo > moore) continue;
        GDesc G;
        if (!pick_group((int)lo, (int)hi, &G)) continue;
        set_group(&G);
        double stop = now() + 2.0;
        if (stop > until) stop = until;
        if (anneal_lift(&cand, p, stop) && cand.n > best->n) copy_graph(best, &cand);
    }
}

/* ---------------------------------------------------------------- grow by two */
static int grow_once(const Graph *best, Graph *work, double until) {
    int n = best->n;
    if (n + 2 > moore_bound_c() || n + 2 > MAXN) return 0;
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
    while (now() < until && best->n + 2 <= moore_bound_c()) {
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
    t_end = t0 + limit * 0.93;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }
    if (!read_start(&best)) complete_bipartite(&best);
    int moore = moore_bound_c();
    if (best.n + 2 <= moore) {
        double split = t0 + (t_end - t0) * 0.5;
        lift_phase(&best, split);
        grow_search(&best, t_end);
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


def _gh_h3():
    """Incidence graph of the split Cayley hexagon H(3): 364 + 364 vertices, degree 4, diameter 6.

    Returns None if no sign convention verifies with lib.is_valid.
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

    if d > 8 or D < 2 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 2.0
    if budget <= 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, budget],
                         stdin_graph=best, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
