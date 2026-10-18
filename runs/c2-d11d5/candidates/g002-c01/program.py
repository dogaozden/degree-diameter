"""Bi-Cayley lift annealing in C with a representative-block reachability cost, then grow-by-two.

New idea in this version: the whole lift search moves into C. A bi-Cayley lift over Z_m x| Z_k2 with
k blocks per side is block-transitive under left multiplication, so the diameter test only needs BFS
from one representative per block (2k bitmask rounds over N vertices). Each annealing step costs about
D*N*d byte operations, so the search runs far more steps than the Python version. Group orders are
sampled over all semidirect products Z_m x| Z_k2 of the target order. The C grow-by-two phase then uses
the remaining time. Every output is checked with lib.is_valid; K_{d,d} is the fallback.
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

#define MAXN 8192
#define MAXD 32
#define MAXW (MAXN / 64)
#define MAXK 4
#define PEN 1000L

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

/* ---- semidirect group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e) ---- */
static int gm, gk, gr;
static int rp[MAXN];

static void set_group(int m, int k2, int r) {
    gm = m; gk = k2; gr = r;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / gk, b = x % gk, c = y / gk, e = y % gk;
    long t = ((long)a + (long)rp[b] * c) % gm;
    return (int)t * gk + (b + e) % gk;
}

/* Uniform-ish random semidirect product of order G (divisor m, random valid r). */
static void pick_group(int G, int *m_out, int *k_out, int *r_out) {
    int divs[64], nd = 0;
    for (int m = 1; m <= G && nd < 64; m++)
        if (G % m == 0) divs[nd++] = m;
    int m = divs[rndint(nd)];
    int k2 = G / m;
    if (m == 1) { *m_out = 1; *k_out = k2; *r_out = 0; return; }
    int cnt = 0;
    for (int r = 1; r < m; r++)
        if (gcd(r, m) == 1 && powmod(r, k2, m) == 1 % m) cnt++;
    int pick = rndint(cnt > 0 ? cnt : 1);
    for (int r = 1; r < m; r++)
        if (gcd(r, m) == 1 && powmod(r, k2, m) == 1 % m) {
            if (pick == 0) { *m_out = m; *k_out = k2; *r_out = r; return; }
            pick--;
        }
    *m_out = 1; *k_out = G; *r_out = 0;
}

/* ---- bi-Cayley lift state: k A-blocks, k B-blocks, d layers ---- */
static int K, GG, NN;
static int P[MAXD][MAXK];      /* P[l][i] = B-block joined to A-block i in layer l */
static int S[MAXD][MAXK];      /* voltage of that dart */
static int nbr[MAXD][MAXN];    /* nbr[l][v] = neighbour of v in layer l */
static unsigned char RR[MAXN], RC[MAXN], RX[MAXN], RY[MAXN];

static void set_dart(int l, int i) {
    int G = GG;
    int j = P[l][i], s = S[l][i];
    for (int x = 0; x < G; x++) {
        int a = i * G + x;
        int b = (K + j) * G + gmul(x, s);
        nbr[l][a] = b;
        nbr[l][b] = a;
    }
}

/* Reach from one representative per block (left-multiplication is an automorphism).
 * Cost = number of (representative, vertex) pairs at distance > D, plus duplicate-dart penalty. */
static long eval_cost(unsigned char *out) {
    int N = NN, G = GG, Kb = 2 * K;
    unsigned char *cur = RX, *nxt = RY;
    memset(cur, 0, (size_t)N);
    for (int b = 0; b < Kb; b++) cur[b * G] = (unsigned char)(1u << b);
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            unsigned char x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        unsigned char *t = cur; cur = nxt; nxt = t;
        if (!changed) break;
    }
    long c = 0;
    for (int v = 0; v < N; v++) c += Kb - __builtin_popcount(cur[v]);
    memcpy(out, cur, (size_t)N);
    long dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return c + PEN * dup;
}

static int anneal(int k, int G, long iters, double deadline, long patience) {
    K = k; GG = G; NN = 2 * k * G;
    int full = (1 << (2 * k)) - 1;
    int tmp[MAXK];
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) tmp[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1), t = tmp[i];
            tmp[i] = tmp[j]; tmp[j] = t;
        }
        for (int i = 0; i < k; i++) { P[l][i] = tmp[i]; S[l][i] = rndint(G); }
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) set_dart(l, i);
    long cost = eval_cost(RR);
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best_cost = cost, last = 0;
    for (long t = 0; t < iters && cost > 0; t++) {
        if ((t & 31) == 0 && now() > deadline) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;
        int l = rndint(d);
        if (k >= 2 && rnd01() < 0.25) {
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int s = P[l][i1]; P[l][i1] = P[l][i2]; P[l][i2] = s;
            set_dart(l, i1); set_dart(l, i2);
            long c2 = eval_cost(RC);
            if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
                cost = c2;
                memcpy(RR, RC, (size_t)NN);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                s = P[l][i1]; P[l][i1] = P[l][i2]; P[l][i2] = s;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }
        int i = -1;
        if (rnd01() < 0.4) {
            int v = -1;
            for (int tries = 0; tries < 50; tries++) {
                int w = rndint(NN);
                if (RR[w] != full) { v = w; break; }
            }
            if (v >= 0) {
                int blk = v / G;
                if (blk < k) i = blk;
                else for (int ii = 0; ii < k; ii++)
                    if (P[l][ii] == blk - k) { i = ii; break; }
            }
        }
        if (i < 0) i = rndint(k);
        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = eval_cost(RC);
        if (c2 <= cost || rnd01() < exp((double)(cost - c2) / temp)) {
            cost = c2;
            memcpy(RR, RC, (size_t)NN);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static int build_graph(Graph *g) {
    g->n = NN;
    for (int v = 0; v < NN; v++) { g->deg[v] = 0; g->side[v] = v >= K * GG; }
    for (int v = 0; v < NN; v++)
        for (int l = 0; l < d; l++) {
            int u = nbr[l][v];
            if (v < u && !has_edge(g, v, u)) add_edge(g, v, u);
        }
    return is_valid(g);
}

static int trials[MAXK + 1], wins[MAXK + 1];

static void lift_search(Graph *best, double until) {
    static Graph cand;
    long mo = moore_bound();
    int fails = 0;
    while (now() < until) {
        int k;
        if (rnd01() < 0.2) k = 1 + rndint(MAXK);
        else {
            double bs = -1.0;
            k = 1;
            for (int c = 1; c <= MAXK; c++) {
                double sc = (wins[c] + 1.0) / (trials[c] + 2.0) + 0.02 * rnd01();
                if (sc > bs) { bs = sc; k = c; }
            }
        }
        int base = best->n / (2 * k);
        int G = base + 1 + rndint(base / 16 + 2);
        if ((long)2 * k * G > mo || 2 * k * G > MAXN) {
            if (++fails > 500) break;
            continue;
        }
        int m, k2, r;
        pick_group(G, &m, &k2, &r);
        set_group(m, k2, r);
        trials[k]++;
        double left = until - now();
        double slice = left / 4.0;
        if (slice < 1.5) slice = 1.5;
        double dl = now() + slice;
        if (dl > until) dl = until;
        if (anneal(k, G, 200000, dl, 3000) && build_graph(&cand) && cand.n > best->n) {
            copy_graph(best, &cand);
            wins[k]++;
        }
    }
}

/* ---- grow-by-two with edge-swap annealing (from the previous engine) ---- */
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
    t_end = t0 + limit * 0.9 - 0.2;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best;
    if (d < 1 || D < 1 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);

    if (D >= 2 && d >= 3) {
        lift_search(&best, t0 + (t_end - t0) * 0.8);
    }
    if (D >= 2 && best.n + 2 <= moore_bound() && best.n + 2 <= MAXN) {
        grow_search(&best, t_end);
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def known_start(d, D):
    """Exact constructions for small cases, or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2 and is Moore-optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D == 2:
        return best

    exact = known_start(d, D)
    if exact is not None:
        consider(exact[0], exact[1])
        return best

    if D == 3 and d >= 4 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass

    limit = time_limit * 0.85 - 3.0 - (time.monotonic() - t0)
    if d > 30 or limit < 2.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(limit, 2)],
                         stdin_graph=best, timeout=limit + 10.0)
        n, e = lib.parse_graph_text(text)
        consider(n, e)
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
