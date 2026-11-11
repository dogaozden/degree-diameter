"""Combined search: exact Moore/record constructions from Python, then C runs bi-Cayley
lift annealing (layered permutations over Z_m x| Z_k2) and grow-by-two from the best graph.
build() always returns a graph that lib.is_valid accepts, falling back to K_{d,d}."""
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core.
 * Usage: prog d D seed time_limit < start_graph
 * stdin: "n m" + m edges, or "0 0". stdout: "n m" + edges of the best valid graph.
 *
 * Phase 1 (bi-Cayley annealing): vertices A_{i,g} = i*G+g (i<k), B_{j,h} = (k+j)*G+h.
 *   Each of d layers is a bijection between A-blocks and B-blocks with a group voltage s,
 *   A_{i,g} ~ B_{j,g*s}. Every vertex gets degree d. Left multiplication is an automorphism,
 *   so diameter is checked from the 2k block representatives with bitmasks.
 * Phase 2 (grow-by-two): add one vertex per side and anneal degree-preserving swaps.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 9600
#define MAXD 32
#define MAXW ((MAXN + 63) / 64)
#define MAXK 6
#define MAXG (MAXN / 2)
#define PEN 1000
#define BC_ITERS 5000
#define BC_PATIENCE 1200

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;
static double T_END;

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

static int gcd_int(int a, int b) {
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

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static int badv[MAXN];

/* Number of unordered pairs at distance > D; sets badv[v] = far vertices of v. */
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

static void complete_bipartite(Graph *g) {
    g->n = 2 * d;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= d; }
    for (int a = 0; a < d; a++)
        for (int b = 0; b < d; b++) add_edge(g, a, d + b);
}

/* ------------------------------------------------------------ groups */

/* Z_m x|_r Z_k2: element a*k2+b, (a,b)(c,e) = (a + r^b c mod m, b+e mod k2). */
typedef struct {
    int m, k2, r;
    int rp[64];
} Grp;

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k2, b = x % g->k2, c = y / g->k2, e = y % g->k2;
    long t = (a + (long)g->rp[b] * c) % g->m;
    return (int)t * g->k2 + (b + e) % g->k2;
}

static const int K2C[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(int target, Grp *g) {
    for (int att = 0; att < 300; att++) {
        int k2 = K2C[rndint(20)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if ((long)m * k2 > MAXG) continue;
        int r = -1;
        if (k2 == 1) r = 1;
        else if (rndint(10) == 0) r = 1;
        else if (k2 == 2 && rndint(3) == 0) r = m - 1;
        else {
            for (int tr = 0; tr < 60 && m > 2; tr++) {
                int c = 2 + rndint(m - 2);
                if (gcd_int(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        if (r < 0) continue;
        if (gcd_int(r, m) != 1 || powmod(r, k2, m) != 1 % m) continue;
        g->m = m;
        g->k2 = k2;
        g->r = r;
        g->rp[0] = 1 % m;
        for (int b = 1; b < k2; b++) g->rp[b] = (int)((long)g->rp[b - 1] * r % m);
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ bi-Cayley search */

typedef struct {
    int k, G, N;
    Grp g;
    int lay[MAXD][MAXK];
    int S[MAXD][MAXK];
} BC;

static int nbr[MAXD][MAXN];
static uint64_t Rcur[MAXN], Rnew[MAXN], Rtmp[MAXN];
static int bad_list[MAXN];

/* Write layer l's matching for A-block i (and its B-block partners). */
static void set_dart(BC *st, int l, int i) {
    int k = st->k, G = st->G, j = st->lay[l][i], s = st->S[l][i];
    int Bbase = (k + j) * G;
    for (int x = 0; x < G; x++) {
        int A = i * G + x;
        int B = Bbase + gmul(&st->g, x, s);
        nbr[l][A] = B;
        nbr[l][B] = A;
    }
}

/* Duplicate keys (i, lay, S) within the same A-block: they would create multi-edges. */
static int bc_dups(const BC *st) {
    int k = st->k, K = d * k, cnt = 0;
    for (int p = 0; p < K; p++) {
        int l1 = p / k, i1 = p % k;
        for (int q = 0; q < p; q++) {
            int l2 = q / k, i2 = q % k;
            if (i1 == i2 && st->lay[l1][i1] == st->lay[l2][i2] && st->S[l1][i1] == st->S[l2][i2])
                cnt++;
        }
    }
    return cnt;
}

/* Reachability bitmasks; returns the number of unreached (block representative, vertex) pairs. */
static long bc_reach(const BC *st, uint64_t *out) {
    int N = st->N, G = st->G, kk = st->k;
    uint64_t *cur = out, *nxt = Rtmp;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * kk; b++) cur[(size_t)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    if (cur != out) memcpy(out, cur, sizeof(uint64_t) * (size_t)N);
    long unr = 0;
    int full_bits = 2 * kk;
    for (int v = 0; v < N; v++) unr += full_bits - __builtin_popcountll(out[v]);
    return unr;
}

static long bc_cost(const BC *st, uint64_t *out) {
    int dp = bc_dups(st);
    long unr = bc_reach(st, out);
    return unr + (long)PEN * dp;
}

static int accept_move(long c2, long cost, double temp) {
    if (c2 <= cost) return 1;
    return rnd01() < exp(-(double)(c2 - cost) / temp);
}

/* Simulated annealing on layers and voltages. Returns 1 if a valid lift was found;
 * then nbr[][] holds it. */
static int bc_search(BC *st, int iters, int patience, double until) {
    int k = st->k, G = st->G, N = st->N;
    uint64_t full = (1ULL << (2 * k)) - 1;
    int perm[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            st->lay[l][i] = perm[i];
            st->S[l][i] = rndint(G);
        }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(st, l, i);

    long cost = bc_cost(st, Rcur);
    double c0 = cost > 1 ? (double)cost : 1.0;
    long best_cost = cost;
    int last = 0;

    for (int t = 0; t < iters && cost > 0; t++) {
        if (t - last > patience) break;
        if ((t & 7) == 0 && now() > until) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / iters);
        if (temp < 0.5) temp = 0.5;
        long c2;
        if (k >= 2 && rnd01() < 0.25) {
            /* layer-swap move */
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = st->lay[l][i1];
            st->lay[l][i1] = st->lay[l][i2];
            st->lay[l][i2] = tmp;
            set_dart(st, l, i1);
            set_dart(st, l, i2);
            c2 = bc_cost(st, Rnew);
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                memcpy(Rcur, Rnew, sizeof(uint64_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = st->lay[l][i1];
                st->lay[l][i1] = st->lay[l][i2];
                st->lay[l][i2] = tmp;
                set_dart(st, l, i1);
                set_dart(st, l, i2);
            }
        } else {
            /* voltage move: defect-targeted with probability 0.4 */
            int l = -1, i = -1, targeted = 0;
            if (rnd01() < 0.4) {
                int nbad = 0;
                for (int v = 0; v < N; v++)
                    if (Rcur[v] != full) bad_list[nbad++] = v;
                if (nbad > 0) {
                    int u = bad_list[rndint(nbad)];
                    int block = u / G;
                    l = rndint(d);
                    if (block < k) i = block;
                    else {
                        for (int ii = 0; ii < k; ii++)
                            if (st->lay[l][ii] == block - k) { i = ii; break; }
                        if (i < 0) i = rndint(k);
                    }
                    targeted = 1;
                }
            }
            if (!targeted) { l = rndint(d); i = rndint(k); }
            int old = st->S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            st->S[l][i] = nw;
            set_dart(st, l, i);
            c2 = bc_cost(st, Rnew);
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                memcpy(Rcur, Rnew, sizeof(uint64_t) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                st->S[l][i] = old;
                set_dart(st, l, i);
            }
        }
    }
    return cost == 0;
}

static void graph_from_bc(const BC *st, Graph *g) {
    int kG = st->k * st->G;
    g->n = st->N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= kG);
    }
    for (int l = 0; l < d; l++)
        for (int A = 0; A < kG; A++) add_edge(g, A, nbr[l][A]);
}

static int pick_k(const int *trials, const int *wins) {
    if (rnd01() < 0.2) return 1 + rndint(MAXK);
    int bk = 1;
    double bv = -1.0;
    for (int k = 1; k <= MAXK; k++) {
        double v = (wins[k] + 1.0) / (trials[k] + 2.0) + 0.02 * rnd01();
        if (v > bv) { bv = v; bk = k; }
    }
    return bk;
}

static void bicayley_phase(Graph *best, double until) {
    static BC st;
    static Grp grp;
    static Graph cand;
    int trials[MAXK + 1], wins[MAXK + 1];
    memset(trials, 0, sizeof trials);
    memset(wins, 0, sizeof wins);
    long moore = moore_bound();
    int fails = 0;
    while (now() < until && best->n < moore) {
        int k = pick_k(trials, wins);
        int base = best->n / (2 * k);
        int spread = base / 8 + 1;
        int target = base + 1 + rndint(spread);
        if (target < 2) target = 2;
        if (!sample_group(target, &grp)) {
            if (++fails > 1000) return;
            continue;
        }
        int G = grp.m * grp.k2;
        long N = 2L * k * G;
        if (N <= best->n || N > MAXN || N > moore) continue;
        st.k = k;
        st.G = G;
        st.N = (int)N;
        st.g = grp;
        trials[k]++;
        if (bc_search(&st, BC_ITERS, BC_PATIENCE, until)) {
            graph_from_bc(&st, &cand);
            if (cand.n > best->n && is_valid(&cand)) {
                copy_graph(best, &cand);
                wins[k]++;
            }
        }
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
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    T_END = t0 + limit * 0.93;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || D < 1) { printf("1 0\n"); return 0; }
    if (D == 1 || d > MAXD) { printf("2 1\n0 1\n"); return 0; }

    static Graph best;
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && best.n < moore_bound()) {
        double t1 = t0 + 0.8 * (T_END - t0);
        bicayley_phase(&best, t1);
        if (best.n > 0) grow_search(&best, T_END);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _exact(d, D):
    """Best exact construction Python knows for (d, D): Moore graph or record-order graph, else None."""
    if D == 3:
        if d - 1 >= 2 and lib.is_prime_power(d - 1):
            return lib.projective_plane_incidence(d - 1)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    start = None
    try:
        ex = _exact(d, D)
    except ValueError:
        ex = None
    if ex is not None and ex[0] > best[0] and lib.is_valid(ex[0], ex[1], d, D):
        best = ex
        start = ex

    if best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.85 * time_limit - 2.5 - (time.monotonic() - t0)
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=start, timeout=budget + 4)
        out = lib.parse_graph_text(text)
    except Exception:
        return best

    if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
        best = out
    return best
