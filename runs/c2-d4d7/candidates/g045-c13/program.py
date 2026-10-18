"""Bi-Cayley (Haar-type) search over metacyclic and PSL/PGL(2,p)-based groups, then grow-by-two.

Changes from the parent:
- The Z_k voltage covers and the fibre-lift search are removed. The new core is a bi-Cayley search.
  A bi-Cayley graph over a group G of order N has vertices A_x and B_y (x, y in G). A_x joins B_{xs}
  for s in S, where S is a set of d distinct group elements. It is d-regular and bipartite, with 2N vertices.
- Left multiplication is an automorphism that is transitive on each side, so diameter <= D holds iff
  BFS from A_e and from B_e reaches everything within D. Each evaluation is therefore two cheap BFS runs.
- Groups: semidirect products Z_m x| Z_k (preferring non-abelian actions), and PSL/PGL(2,p) for
  p = 5, 7, 11 times a cyclic Z_c, all built as multiplication tables.
- Simulated annealing over S (one element swapped per move) with the unreached-pair count as the objective.
  Groups are resampled on restart, and the order N ranges over values that beat the current best.
- Time split: about 75% bi-Cayley search, then grow-by-two on the best graph. Python keeps the
  algebraic starts (PG(2,q), W(q), H(3)) and validates every output. Any failure falls back to the best valid graph.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Bi-Cayley (Haar-type) diameter search core.
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v", or "0 0" for none.
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
#define GMAX 1100
#define NBG 5
#define HS 8192
#define STEPS 4000

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

/* ---------------------------------------------------------------- group tables
 * The current group is a multiplication table GT[x*GN+y] with identity 0.
 * GINV holds inverses. */
static int GN;
static int GT[GMAX * GMAX];
static int GINV[GMAX];
static int RPW[GMAX];

static void compute_inverses(void) {
    for (int x = 0; x < GN; x++)
        for (int y = 0; y < GN; y++)
            if (GT[x * GN + y] == 0) { GINV[x] = y; break; }
}

/* Z_m x|_r Z_k: element a*k + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static void set_semidirect(int m, int k, int r) {
    int N = m * k;
    GN = N;
    RPW[0] = 1 % m;
    for (int b = 1; b < k; b++) RPW[b] = (int)((long)RPW[b - 1] * r % m);
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            long v = ((long)a + (long)RPW[b] * c) % m;
            GT[x * N + y] = (int)(v * k + (b + e) % k);
        }
    }
    compute_inverses();
}

static int *BT[NBG];
static int BO[NBG];

/* Permutation groups on p+1 points, built by closure of generators. */
typedef struct { unsigned char p[12]; } Perm;
static Perm PE[GMAX];
static uint64_t hk[HS];
static int hv[HS];

static uint64_t pkey(const unsigned char *a, int s) {
    uint64_t k = 0;
    for (int i = 0; i < s; i++) k |= (uint64_t)a[i] << (4 * i);
    return k;
}

static unsigned hslot(uint64_t key) {
    return (unsigned)((key * 0x9E3779B97F4A7C15ULL) >> 51);
}

static int hfind(uint64_t key) {
    unsigned h = hslot(key);
    while (hv[h]) {
        if (hk[h] == key) return hv[h] - 1;
        h = (h + 1) & (HS - 1);
    }
    return -1;
}

static void hput(uint64_t key, int idx) {
    unsigned h = hslot(key);
    while (hv[h]) h = (h + 1) & (HS - 1);
    hk[h] = key;
    hv[h] = idx + 1;
}

/* Closure of the generators of PSL(2,p) (pgl = 0) or PGL(2,p) (pgl = 1) on P^1(F_p). */
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

    memset(hv, 0, sizeof hv);
    memset(&PE[0], 0, sizeof(Perm));
    for (int x = 0; x < s; x++) PE[0].p[x] = (unsigned char)x;
    hput(pkey(PE[0].p, s), 0);
    int n = 1;
    for (int qi = 0; qi < n; qi++) {
        for (int k = 0; k < ng; k++) {
            Perm h;
            memset(&h, 0, sizeof h);
            for (int x = 0; x < s; x++) h.p[x] = PE[qi].p[gen[k].p[x]];
            uint64_t key = pkey(h.p, s);
            if (hfind(key) < 0) {
                if (n >= GMAX) return 0;
                PE[n] = h;
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
            for (int x = 0; x < s; x++) h.p[x] = PE[i].p[PE[j].p[x]];
            int idx = hfind(pkey(h.p, s));
            tab[(size_t)i * ord + j] = idx < 0 ? 0 : idx;
        }
    *ordp = ord;
    return tab;
}

static void init_bases(void) {
    static const int BP[NBG] = {5, 5, 7, 7, 11};
    static const int BG[NBG] = {0, 1, 0, 1, 0};
    for (int b = 0; b < NBG; b++) {
        BO[b] = 0;
        BT[b] = make_base_table(BP[b], BG[b], &BO[b]);
        if (!BT[b]) BO[b] = 0;
    }
}

/* Direct product of base group b with Z_c: element x*c + t, (x,t)(y,u) = (xy, t+u). */
static void set_product(int b, int c) {
    int o = BO[b], N = o * c;
    const int *bt = BT[b];
    GN = N;
    for (int x = 0; x < o; x++)
        for (int t = 0; t < c; t++)
            for (int y = 0; y < o; y++)
                for (int u = 0; u < c; u++)
                    GT[(x * c + t) * N + (y * c + u)] = bt[x * o + y] * c + (t + u) % c;
    compute_inverses();
}

static int divs[GMAX + 1];
static int rcand[GMAX + 1];

/* Choose a random semidirect Z_m x| Z_k of order N, preferring non-abelian actions. */
static int choose_semidirect(int N, int *mo, int *ko, int *ro) {
    int nd = 0;
    for (int m = 1; m <= N; m++)
        if (N % m == 0) divs[nd++] = m;
    for (int tries = 0; tries < 16; tries++) {
        int m = divs[rndint(nd)];
        int k = N / m;
        int nr = 0;
        if (m == 1) {
            rcand[nr++] = 0;
        } else {
            for (int r = 1; r < m; r++) {
                if (gcd(r, m) != 1) continue;
                if (powmod(r, k, m) != 1 % m) continue;
                rcand[nr++] = r;
            }
        }
        if (nr == 0) continue;
        int nontriv = 0;
        for (int i = 0; i < nr; i++) if (rcand[i] != 1) nontriv++;
        int r = rcand[0];
        if (nontriv > 0 && rndint(10) < 8) {
            int t = rndint(nontriv);
            for (int i = 0; i < nr; i++)
                if (rcand[i] != 1) {
                    if (t == 0) { r = rcand[i]; break; }
                    t--;
                }
        } else {
            r = rcand[rndint(nr)];
        }
        *mo = m;
        *ko = k;
        *ro = r;
        return 1;
    }
    return 0;
}

static int pick_group(int N) {
    if (rndint(2) == 0) {
        int opts[NBG], no = 0;
        for (int b = 0; b < NBG; b++)
            if (BO[b] && N % BO[b] == 0) opts[no++] = b;
        if (no > 0) {
            int b = opts[rndint(no)];
            set_product(b, N / BO[b]);
            return 1;
        }
    }
    int m, k, r;
    if (!choose_semidirect(N, &m, &k, &r)) return 0;
    set_semidirect(m, k, r);
    return 1;
}

/* ---------------------------------------------------------------- bi-Cayley search
 * Vertices: A_x = x (0..N-1), B_y = N + y. A_x ~ B_{x s} for s in S.
 * Left multiplication is transitive on each side, so BFS from A_e and B_e is exact. */
static int dist_h[2 * GMAX], q_h[2 * GMAX];

static int unreached(int N, const int *S, int src) {
    int M2 = 2 * N;
    for (int v = 0; v < M2; v++) dist_h[v] = -1;
    int head = 0, tail = 0;
    dist_h[src] = 0;
    q_h[tail++] = src;
    while (head < tail) {
        int v = q_h[head++];
        if (dist_h[v] >= D) continue;
        int nd = dist_h[v] + 1;
        if (v < N) {
            const int *row = GT + (size_t)v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[S[i]];
                if (dist_h[u] < 0) { dist_h[u] = nd; q_h[tail++] = u; }
            }
        } else {
            const int *row = GT + (size_t)(v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[GINV[S[i]]];
                if (dist_h[u] < 0) { dist_h[u] = nd; q_h[tail++] = u; }
            }
        }
    }
    return M2 - tail;
}

static int objective(int N, const int *S) {
    return unreached(N, S, 0) + unreached(N, S, N);
}

static int cur[MAXD], trial[MAXD];

static int in_set(const int *S, int k, int g) {
    for (int i = 0; i < k; i++)
        if (S[i] == g) return 1;
    return 0;
}

/* Simulated annealing over the connection set S (d distinct elements of the current group). */
static int anneal(int N, double until, int *bestS) {
    for (int i = 0; i < d; i++) {
        int g;
        do g = rndint(N); while (in_set(cur, i, g));
        cur[i] = g;
    }
    int f = objective(N, cur);
    int bf = f;
    memcpy(bestS, cur, sizeof(int) * (size_t)d);
    for (int s = 0; s < STEPS && f > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        double T = 0.8 * (1.0 - (double)s / STEPS) + 0.02;
        memcpy(trial, cur, sizeof(int) * (size_t)d);
        int g;
        do g = rndint(N); while (in_set(cur, d, g));
        trial[rndint(d)] = g;
        int nf = objective(N, trial);
        if (nf <= f || rnd01() < exp((double)(f - nf) / T)) {
            memcpy(cur, trial, sizeof(int) * (size_t)d);
            f = nf;
            if (f < bf) {
                bf = f;
                memcpy(bestS, cur, sizeof(int) * (size_t)d);
            }
        }
    }
    return bf == 0;
}

static void build_haar(Graph *g, int N, const int *S) {
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + GT[x * N + S[i]]);
}

static void haar_search(Graph *best, double until) {
    static Graph cand;
    static int bestS[MAXD];
    long moore = moore_bound();
    long Nm = moore / 2;
    int Nmax = Nm < GMAX ? (int)Nm : GMAX;
    while (now() < until) {
        int Nlo = best->n / 2 + 1;
        if (Nlo < d + 1) Nlo = d + 1;
        if (Nlo > Nmax) return;
        int span = Nlo / 6 + 6;
        int Nhi = Nlo + span;
        if (Nhi > Nmax) Nhi = Nmax;
        int N = Nlo + rndint(Nhi - Nlo + 1);
        if (!pick_group(N)) continue;
        if (anneal(N, until, bestS)) {
            build_haar(&cand, N, bestS);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ---------------------------------------------------------------- grow by two */
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.9;
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
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        init_bases();
        double span = t_end - t0;
        haar_search(&best, t0 + 0.75 * span);
        if (best.n < moore_bound()) grow_search(&best, t_end);
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
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])
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
