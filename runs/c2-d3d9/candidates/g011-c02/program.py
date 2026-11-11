"""Combined search: Cayley (bi-Cayley) random search, voltage lifts over metacyclic groups, and grow-by-two.

Phases inside the C engine, sharing one valid best graph:
  1. Cayley phase: bi-Cayley graphs over Z_m x| Z_k (nonabelian groups first). Each candidate is checked with two
     BFS runs (from A_1 and B_1), which suffice by vertex-transitivity. The winner is re-verified by full bad_pairs.
  2. Lift phase: voltage lifts over base multigraphs with p = 1..4 vertices per side. Voltages are hill-climbed on the
     number of bad pairs. Group orders are aimed at record_goal + 2 and above, so lifts of 508..516 vertices are tried
     (2pN with small p gives many such orders).
  3. Grow phase: insert one vertex per side and anneal edge swaps.

Python builds only the trivial starts, runs the engine once, and checks every output with lib.is_valid.
"""
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

#define MAXN 2200
#define MAXD 16
#define MAXW ((MAXN + 63) / 64)
#define MAXG 1100
#define MAXP 4
#define MAXCAND 8192

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct { int m, k, r; } Grp;
typedef struct { int i, j, g; } Dart;

static int d, D;
static double t_end;
static long goal_n = 0;

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

/* Largest possible order of a bipartite graph with max degree d and diameter D. */
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

static int has_edge(const Graph *g, int u, int v) {
    for (int i = 0; i < g->deg[u]; i++)
        if (g->adj[u][i] == v) return 1;
    return 0;
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

/* Number of unordered pairs at distance > D (0 means diameter <= D). */
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

/* ------------------------------------------------------------ input / output */

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

/* K_{d,d}: valid for D >= 2. */
static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups Z_m x| Z_k */

/* Element (a, b) is the int a*k + b; (a,b)(c,e) = (a + r^b c mod m, b + e mod k). */
static Grp curG;
static int rpw[MAXG];
static int NN;
static int MT[MAXG * MAXG]; /* multiplication table, used by the Cayley phase */
static int INV[MAXG];

static void set_rp(Grp G) {
    curG = G;
    NN = G.m * G.k;
    rpw[0] = 1 % G.m;
    for (int b = 1; b < G.k; b++) rpw[b] = (int)((long)rpw[b - 1] * G.r % G.m);
}

static int gmul(int x, int y) {
    int k = curG.k, m = curG.m;
    int a = x / k, b = x % k, c = y / k, e = y % k;
    return (int)(((long)a + (long)rpw[b] * c) % m) * k + (b + e) % k;
}

/* All groups of order N: nonabelian ones first. Returns count; *nonab = number of nonabelian ones. */
static int enum_groups(int N, Grp *out, int *nonab) {
    static Grp ab[MAXCAND];
    int nab = 0, cnt = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        int rmax = m > 1 ? m : 2;
        for (int r = 1; r < rmax; r++) {
            if (m > 1 && gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            Grp G = {m, k, r};
            if (m > 1 && r != 1) {
                if (cnt < MAXCAND) out[cnt++] = G;
            } else {
                if (nab < MAXCAND) ab[nab++] = G;
            }
        }
    }
    *nonab = cnt;
    for (int i = 0; i < nab && cnt < MAXCAND; i++) out[cnt++] = ab[i];
    return cnt;
}

/* Uniform group of order N, with preference (80%) for nonabelian ones. Sets curG and rpw. */
static int random_group(int N, Grp *G) {
    static Grp buf[MAXCAND];
    int nonab = 0;
    int cnt = enum_groups(N, buf, &nonab);
    if (cnt == 0) return 0;
    int use_nonab = nonab > 0 && (nonab == cnt || rndint(100) < 80);
    *G = use_nonab ? buf[rndint(nonab)] : buf[nonab + rndint(cnt - nonab)];
    set_rp(*G);
    return 1;
}

static void build_mt(Grp G) {
    set_rp(G);
    int n = NN;
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            MT[x * n + y] = gmul(x, y);
    for (int x = 0; x < n; x++)
        for (int y = 0; y < n; y++)
            if (MT[x * n + y] == 0) { INV[x] = y; break; }
}

/* ------------------------------------------------------------ Cayley (bi-Cayley) phase */

static int dist_[MAXN], queue_[MAXN];

/* 1 iff every vertex of the bi-Cayley graph is within D of src.
 * A_x = x, B_h = NN + h, A_x ~ B_{x s}, B_h ~ A_{h s^-1}. */
static int reach_all(const int *S, int src) {
    int n = NN, V = 2 * n;
    for (int i = 0; i < V; i++) dist_[i] = -1;
    int head = 0, tail = 0;
    dist_[src] = 0;
    queue_[tail++] = src;
    while (head < tail) {
        int v = queue_[head++];
        int dv = dist_[v];
        if (dv >= D) continue;
        if (v < n) {
            for (int i = 0; i < d; i++) {
                int u = n + MT[v * n + S[i]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        } else {
            int h = v - n;
            for (int i = 0; i < d; i++) {
                int u = MT[h * n + INV[S[i]]];
                if (dist_[u] < 0) { dist_[u] = dv + 1; queue_[tail++] = u; }
            }
        }
    }
    return tail == V;
}

/* Random connection set S = {0, s_1, ..., s_{d-1}} of distinct elements (WLOG 0 in S). */
static void pick_set(int n, int *S) {
    S[0] = 0;
    for (int i = 1; i < d; i++) {
        for (;;) {
            int x = 1 + rndint(n - 1);
            int dup = 0;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { dup = 1; break; }
            if (!dup) { S[i] = x; break; }
        }
    }
}

/* Random search for a good (group, S) of order n. Returns 1 and fills outG, outS on success. */
static int cayley_attempt(int n, double until, Grp *outG, int *outS) {
    static Grp grps[MAXCAND];
    int nonab = 0;
    int ng = enum_groups(n, grps, &nonab);
    int S[MAXD];
    if (ng == 0) return 0;
    while (now() < until) {
        for (int gi = 0; gi < ng; gi++) {
            if (now() >= until) return 0;
            build_mt(grps[gi]);
            for (int t = 0; t < 3000; t++) {
                if ((t & 255) == 0 && now() >= until) break;
                pick_set(n, S);
                if (reach_all(S, 0) && reach_all(S, n)) {
                    *outG = grps[gi];
                    memcpy(outS, S, sizeof(int) * (size_t)d);
                    return 1;
                }
            }
        }
    }
    return 0;
}

static void add_group_graph(Graph *g, int n, const int *S) {
    g->n = 2 * n;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= n; }
    for (int x = 0; x < n; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, n + MT[x * n + S[i]]);
}

static void cayley_search(Graph *best, double until) {
    static Graph cand;
    long moore = moore_bound();
    long nmax = moore / 2;
    if (nmax > MAXG - 1) nmax = MAXG - 1;
    double T = until - now();
    if (T <= 0) return;
    double slice = T / 20.0;
    if (slice < 0.3) slice = 0.3;
    if (slice > 2.0) slice = 2.0;
    while (now() < until) {
        long lo = best->n / 2 + 1;
        if (lo < d + 1) lo = d + 1;
        if (lo > nmax) return;
        long n = lo + rndint(3);
        if (n > nmax) n = lo;
        double att_end = now() + slice;
        if (att_end > until) att_end = until;
        Grp G;
        int S[MAXD];
        if (cayley_attempt((int)n, att_end, &G, S)) {
            build_mt(G);
            add_group_graph(&cand, (int)n, S);
            if (cand.n > best->n && is_valid(&cand)) copy_graph(best, &cand);
        }
    }
}

/* ------------------------------------------------------------ voltage lifts */

/* Random d-regular bipartite base multigraph on p + p vertices (sum of d permutation matrices). */
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

static void build_lift(Graph *g, int p, int N, const Dart *dt, int nd) {
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dt[t].i * N + x, p * N + dt[t].j * N + gmul(x, dt[t].g));
}

/* A voltage not used by another dart between the same pair of base vertices. */
static int fresh_voltage(const Dart *dt, int nd, int skip, int i, int j, int N) {
    for (;;) {
        int g = rndint(N), clash = 0;
        for (int t = 0; t < nd; t++)
            if (t != skip && dt[t].i == i && dt[t].j == j && dt[t].g == g) { clash = 1; break; }
        if (!clash) return g;
    }
}

/* Hill-climb on the voltages of a random base graph. On success g is a valid lift. */
static int lift_try(Graph *g, int p, int N, const Grp *G, int steps) {
    int M[MAXP][MAXP];
    Dart dt[MAXD * MAXP];
    int nd = 0;
    set_rp(*G);
    make_base(p, M);
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < M[i][j]; c++) {
                dt[nd].i = i;
                dt[nd].j = j;
                dt[nd].g = c == 0 ? 0 : fresh_voltage(dt, nd, -1, i, j, N);
                nd++;
            }
    build_lift(g, p, N, dt, nd);
    long bad = bad_pairs(g);
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 15) == 0 && now() > t_end) return 0;
        int t = rndint(nd);
        int old = dt[t].g;
        dt[t].g = fresh_voltage(dt, nd, t, dt[t].i, dt[t].j, N);
        build_lift(g, p, N, dt, nd);
        long nb = bad_pairs(g);
        if (nb <= bad || rnd01() < 0.01) bad = nb;
        else dt[t].g = old;
    }
    return bad == 0;
}

static void lift_search(Graph *best, double until) {
    static Graph cand;
    Grp G;
    long moore = moore_bound();
    int fails = 0;
    while (now() < until) {
        int r = rndint(20);
        int p = r < 4 ? 1 : r < 9 ? 2 : r < 14 ? 3 : 4;
        long target = best->n + 2;
        /* Most draws aim at record + 2 or a little above, so the result beats the record. */
        if (goal_n > (long)best->n + 2 && rndint(10) < 6) target = goal_n + 2 + 2 * rndint(6);
        if (target > moore) {
            target = best->n + 2;
            if (target > moore) return;
        }
        long base_N = (target + 2 * p - 1) / (2 * p);
        int jitter = 2 + (int)(base_N / 16);
        long N = base_N + rndint(jitter);
        if (best->n == 0) N = d + rndint(3);
        if (N < d || N > MAXG || 2L * p * N > moore || 2L * p * N > MAXN) {
            if (++fails > 3000) return;
            continue;
        }
        Grp G2;
        if (!random_group((int)N, &G2)) {
            if (++fails > 3000) return;
            continue;
        }
        G = G2;
        int steps = 200 + (int)(400000 / (2 * p * N));
        if (lift_try(&cand, p, (int)N, &G, steps) && cand.n > best->n && is_valid(&cand))
            copy_graph(best, &cand);
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
        fprintf(stderr, "usage: %s d D seed time_limit [goal] < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    goal_n = argc > 5 ? atol(argv[5]) : 0;

    double t0 = now();
    t_end = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    if (D < 2) {
        if (d >= 1) printf("2 1\n0 1\n");
        else printf("0 0\n");
        return 0;
    }

    static Graph best;
    read_start(&best);
    long moore = moore_bound();

    if (d >= 2 && best.n < moore) {
        double T = t_end - t0;
        cayley_search(&best, t0 + 0.35 * T);
        lift_search(&best, t0 + 0.80 * T);
        if (best.n > 0) grow_search(&best, t_end);
    }
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''

# Known record orders, passed to the C engine as a search goal.
RECORD_GOAL = {(3, 9): 506}


def known_start(d, D):
    """Best graph Python can build directly for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record graphs of order 2(q^2+q+5)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    known = known_start(d, D)
    best = known if known is not None else lib.haar_graph(d, range(d))  # K_{d,d}
    if not lib.is_valid(best[0], best[1], d, D):
        best = (2, [(0, 1)])  # K_2 is valid for D >= 1 (K_{d,d} needs D >= 2)
    if best[0] >= lib.moore_bound(d, D) or d < 2 or D < 2 or d > 16:
        return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 1.0
    if budget < 1.0:
        return best

    goal = RECORD_GOAL.get((d, D), 0)
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), goal],
                         stdin_graph=known, timeout=budget + 8)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except (RuntimeError, ValueError):
        pass  # keep the valid fallback
    return best
