"""Bi-Cayley search over matrix-type and metacyclic groups, with grow-by-two fallback.

The C engine searches bipartite graphs A_g ~ B_h iff g^{-1}h in S, for a group G
of order N and a connection set S of size d. Groups come from PSL/SL/PGL/GL(2,p)
(p <= 7), direct products of those with cyclic groups, and metacyclic groups.
Left multiplication is an automorphism, so the diameter check needs only two BFS
runs, from A_e and B_e. Simulated annealing on S runs for each group. Bi-Cayley
graphs of order 2N are kept as the best. The remaining time goes to grow-by-two.
The Python side keeps the known constructions and a K_{d,d} fallback, and checks
every returned graph with lib.is_valid.
"""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search: bi-Cayley graphs over matrix groups.
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v": a valid start graph, or "0 0" for none.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Phase 1: pick a group G of order N (metacyclic, PSL/SL/PGL/GL(2,p) with p<=7,
 *   or those times a cyclic group). Anneal a connection set S of d elements so that
 *   A_g ~ B_{gs} has diameter <= D. Check it from A_e and B_e only.
 * Phase 2: grow by two from the best graph with annealed swaps.
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
#define MAXG 1024

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static long moore;
static double t_end;

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

/* ------------------------------------------------------------------ input / output */

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

/* ------------------------------------------------------------------ groups */

/* Current group: order GN, identity EID, table MT, inverses INV. */
static int GN, EID;
static int MT[MAXG * MAXG];
static int INV[MAXG];

/* Saved base group for direct products with cyclic groups. */
static int BMT[MAXG * MAXG];
static int BN, BE;

/* Matrix-group globals. */
static int MP, MKIND;      /* prime p; kind 0 GL, 1 SL, 2 PGL, 3 PSL */
static int IDX[2401];      /* p^4 <= 2401 for p <= 7 */

static int finish_group(void) {
    int N = GN;
    for (int x = 0; x < N; x++) {
        INV[x] = -1;
        if (MT[EID * N + x] != x) return 0;   /* identity check */
    }
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == EID) { INV[x] = y; break; }
    for (int x = 0; x < N; x++)
        if (INV[x] < 0) return 0;
    return 1;
}

static int build_meta(int m, int k, int r) {
    int N = m * k;
    if (N > MAXG || N < 1) return 0;
    long RP[MAXG];
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = RP[b - 1] * r % m;
    GN = N;
    EID = 0;
    for (int x = 0; x < N; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < N; y++) {
            int c = y / k, e = y % k;
            MT[x * N + y] = (int)((((long)a + RP[b] * c) % m) * k + (b + e) % k);
        }
    }
    return finish_group();
}

/* Uniform random metacyclic group Z_m x|_r Z_k with m*k = N. */
static int build_random_meta(int N) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        for (int r = 0; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    return build_meta(bm, bk, br);
}

static void dec(int code, int *a, int *b, int *c, int *e) {
    int p = MP;
    *e = code % p; code /= p;
    *c = code % p; code /= p;
    *b = code % p; code /= p;
    *a = code % p;
}

static int canon_code(int code) {
    if (MKIND == 0 || MKIND == 1) return code;
    int p = MP, a, b, c, e;
    dec(code, &a, &b, &c, &e);
    int best = code;
    for (int s = 1; s < p; s++) {
        if (MKIND == 3 && s != 1 && s != p - 1) continue;
        int c2 = ((((s * a) % p) * p + (s * b) % p) * p + (s * c) % p) * p + (s * e) % p;
        if (c2 < best) best = c2;
    }
    return best;
}

static int in_group(int code) {
    int p = MP, a, b, c, e;
    dec(code, &a, &b, &c, &e);
    int det = ((a * e - b * c) % p + p) % p;
    if (MKIND == 1 || MKIND == 3) return det == 1;
    return det != 0;
}

/* Matrix group over GF(p): kind 0 GL, 1 SL, 2 PGL, 3 PSL. Elements are canonical codes. */
static int build_matrix(int p, int kind) {
    MP = p;
    MKIND = kind;
    int P4 = p * p * p * p;
    if (P4 > 2401) return 0;
    static int elems[MAXG];
    int cnt = 0;
    for (int i = 0; i < P4; i++) IDX[i] = -1;
    for (int code = 0; code < P4; code++) {
        if (!in_group(code)) continue;
        if (canon_code(code) != code) continue;
        if (cnt >= MAXG) return 0;
        IDX[code] = cnt;
        elems[cnt++] = code;
    }
    GN = cnt;
    for (int x = 0; x < cnt; x++) {
        int a1, b1, c1, e1;
        dec(elems[x], &a1, &b1, &c1, &e1);
        for (int y = 0; y < cnt; y++) {
            int a2, b2, c2, e2;
            dec(elems[y], &a2, &b2, &c2, &e2);
            int A = (a1 * a2 + b1 * c2) % p;
            int B = (a1 * b2 + b1 * e2) % p;
            int C = (c1 * a2 + e1 * c2) % p;
            int E = (c1 * b2 + e1 * e2) % p;
            int pc = canon_code(((A * p + B) * p + C) * p + E);
            int z = IDX[pc];
            if (z < 0) return 0;
            MT[x * cnt + y] = z;
        }
    }
    EID = IDX[canon_code(p * p * p + 1)];
    if (EID < 0) return 0;
    return finish_group();
}

static void save_base(void) {
    BN = GN;
    BE = EID;
    memcpy(BMT, MT, sizeof(int) * (size_t)GN * GN);
}

/* Direct product of the saved base with Z_c. */
static int build_product_cyclic(int c) {
    int N = BN * c;
    if (N > MAXG) return 0;
    for (int x = 0; x < N; x++) {
        int g1 = x / c, z1 = x % c;
        for (int y = 0; y < N; y++) {
            int g2 = y / c, z2 = y % c;
            MT[x * N + y] = BMT[g1 * BN + g2] * c + (z1 + z2) % c;
        }
    }
    GN = N;
    EID = BE * c;
    return finish_group();
}

/* Pick a group of order N: metacyclic, or a matrix base (times Z_c) whose order divides N. */
static int make_group(int N) {
    static const int BASE[][3] = {
        {3, 3, 12}, {3, 1, 24}, {3, 2, 24}, {3, 0, 48},
        {5, 3, 60}, {5, 1, 120}, {5, 2, 120}, {5, 0, 480},
        {7, 3, 168}, {7, 1, 336}, {7, 2, 336}
    };
    int nb = (int)(sizeof BASE / sizeof BASE[0]);
    int opts[16], no = 0;
    opts[no++] = -1;
    for (int i = 0; i < nb && no < 16; i++)
        if (N % BASE[i][2] == 0) opts[no++] = i;
    int pick = opts[rndint(no)];
    if (pick < 0) return build_random_meta(N);
    if (!build_matrix(BASE[pick][0], BASE[pick][1])) return build_random_meta(N);
    save_base();
    int c = N / BASE[pick][2];
    if (c == 1) return 1;
    if (build_product_cyclic(c)) return 1;
    return build_random_meta(N);
}

/* ------------------------------------------------------------------ bi-Cayley search */

static int vis[2 * MAXG];
static int vstamp = 0;
static int bq[2 * MAXG];
static int SI_buf[MAXD];

static long bfs_unreached(int src, const int *S, const int *SI) {
    int N = GN, dd = d;
    vstamp++;
    int head = 0, tail = 0;
    vis[src] = vstamp;
    bq[tail++] = src;
    for (int lev = 0; lev < D && head < tail; lev++) {
        int end = tail;
        while (head < end) {
            int v = bq[head++];
            if (v < N) {
                const int *row = MT + (size_t)v * N;
                for (int i = 0; i < dd; i++) {
                    int w = N + row[S[i]];
                    if (vis[w] != vstamp) { vis[w] = vstamp; bq[tail++] = w; }
                }
            } else {
                const int *row = MT + (size_t)(v - N) * N;
                for (int i = 0; i < dd; i++) {
                    int w = row[SI[i]];
                    if (vis[w] != vstamp) { vis[w] = vstamp; bq[tail++] = w; }
                }
            }
        }
    }
    return (long)(2 * N - tail);
}

/* Unreached (source, vertex) pairs from A_e and B_e. Zero means diameter <= D. */
static long bi_cost(const int *S) {
    for (int i = 0; i < d; i++) SI_buf[i] = INV[S[i]];
    return bfs_unreached(EID, S, SI_buf) + bfs_unreached(GN + EID, S, SI_buf);
}

static int in_set(const int *S, int cnt, int x) {
    for (int i = 0; i < cnt; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Anneal a connection set S of d distinct elements. Returns 1 and fills Sout on success. */
static int anneal(int steps, double until, int *Sout) {
    int N = GN, dd = d;
    int S[MAXD];
    for (int i = 0; i < dd; i++) {
        int x;
        do { x = rndint(N); } while (in_set(S, i, x));
        S[i] = x;
    }
    long c = bi_cost(S);
    double T = 3.0;
    for (int s = 0; s < steps && c > 0; s++) {
        if ((s & 511) == 0 && now() > until) break;
        int i = rndint(dd);
        int x = rndint(N);
        if (in_set(S, dd, x)) continue;
        int old = S[i];
        S[i] = x;
        long c2 = bi_cost(S);
        if (c2 <= c || rnd01() < exp(-(double)(c2 - c) / T)) c = c2;
        else S[i] = old;
        T *= 0.9997;
        if (T < 0.3) T = 3.0;
    }
    if (c != 0) return 0;
    for (int i = 0; i < dd; i++) Sout[i] = S[i];
    return 1;
}

/* Bi-Cayley graph: A_g ~ B_{g s} for s in S; sides A = 0, B = 1. */
static void build_bi(Graph *g, const int *S) {
    int N = GN;
    g->n = 2 * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= N; }
    for (int x = 0; x < N; x++)
        for (int i = 0; i < d; i++)
            add_edge(g, x, N + MT[x * N + S[i]]);
}

static Graph best;

static void bicayley_phase(double until) {
    static Graph cand;
    static int S[MAXD];
    int curN = best.n / 2 + 1;
    while (now() < until && best.n < moore) {
        if (curN < d) curN = d;
        if (curN > MAXG || 2L * curN > moore) break;
        int N = curN + rndint(5);
        if (N > MAXG || 2L * N > moore) N = curN;
        if (!make_group(N) || GN != N) { curN++; continue; }
        int ok = 0;
        for (int att = 0; att < 3 && !ok && now() < until; att++)
            ok = anneal(40000, until, S);
        if (ok) {
            build_bi(&cand, S);
            if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
            curN = best.n / 2 + 1;
        } else {
            curN++;
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();
    moore = compute_moore();

    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (best.n < moore) {
        bicayley_phase(t0 + (t_end - t0) * 0.8);
        grow_search(t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


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

    if best[0] >= lib.moore_bound(d, D):
        return best

    # Give C nearly the whole case budget; its own clock covers 95% of this value.
    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 5)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
