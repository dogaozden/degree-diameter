"""Multi-fibre voltage lifts over semidirect groups, annealed with orbit-reduced diameter checks.

The engine searches lifts of a d-regular bipartite base multigraph on p+p fibres (p in 1..6). Fibre
A_i has elements a_{i,x} and fibre B_j has b_{j,y}, x, y in a group G of order N. Dart (t, i) joins
a_{i,x} to b_{sigma_t(i), x*g_{t,i}}, where each sigma_t is a permutation and the pairs
(sigma_t(i), g_{t,i}) are distinct for each i. Left multiplication by G is an automorphism that is
transitive on each fibre, so the diameter check needs BFS only from the 2p fibre identities a_{i,e}
and b_{j,e}. Voltages and permutations are annealed to minimise unreached pairs. Every hit is
verified by an all-pairs check in C and again in Python with lib.is_valid.

p = 1 is the bi-Cayley family used by the previous search, so that family is still covered. Larger p
gives a different family with more freedom per vertex count. Starts are the best algebraic graph
(split Cayley hexagon for D >= 6, projective plane, Araujo-Pardo-Lopez graph), and K_{d,d} is the
last fallback, so every case returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre lift search for bipartite degree-diameter graphs.
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

#define MAXN 8192
#define MAXW (MAXN / 64)
#define MAXD 32
#define MAXP 6
#define STEPS 6000
#define T0 2.0
#define T_MIN 0.2
#define T_DECAY 0.9996

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

/* Number of unordered vertex pairs at distance > D (bitset BFS). */
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

/* ---------------- groups: Z_m x|_r Z_k, element a*k + b ---------------- */

typedef struct {
    int m, k, r;
    int rp[MAXN];   /* rp[b] = r^b mod m */
} Grp;

static Grp G;

static int gmul(const Grp *g, int x, int y) {
    int a = x / g->k, b = x % g->k, c = y / g->k, e = y % g->k;
    return (int)(((long)a + (long)g->rp[b] * c) % g->m) * g->k + (b + e) % g->k;
}

/* Inverse of (a, b) is (-r^{-b} a, -b). */
static int ginv(const Grp *g, int x) {
    int a = x / g->k, b = x % g->k;
    int nb = (g->k - b) % g->k;
    long t = (long)g->rp[nb] * a % g->m;
    int na = (int)((g->m - t) % g->m);
    return na * g->k + nb;
}

/* Sample a semidirect product of order N (reservoir sampling). If want is set,
 * prefer non-abelian ones (r != 1, k > 1). Returns 0 if none exists. */
static int random_group(int N, int want) {
    long cnt = 0;
    int bm = 1, bk = N, br = 0;
    for (int m = 1; m <= N; m++) {
        if (N % m) continue;
        int k = N / m;
        if (m == 1) {
            if (!want) {
                cnt++;
                if (rndint((int)cnt) == 0) { bm = 1; bk = N; br = 0; }
            }
            continue;
        }
        for (int r = 1; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, k, m) != 1) continue;
            if (want && (r == 1 || k == 1)) continue;
            cnt++;
            if (rndint((int)cnt) == 0) { bm = m; bk = k; br = r; }
        }
    }
    if (cnt == 0) return 0;
    G.m = bm;
    G.k = bk;
    G.r = br;
    G.rp[0] = 1 % bm;
    for (int b = 1; b < bk; b++) G.rp[b] = (int)((long)G.rp[b - 1] * br % bm);
    return 1;
}

/* ---------------- multi-fibre lift state ----------------
 * Row t (0..d-1) and source fibre i (0..p-1) form dart (t, i):
 *   a_{i,x} -- b_{sig[t][i], x * gv[t][i]} for all x in G.
 * sinv[t][j] is the source fibre whose row-t dart lands in fibre j.
 * Constraint: for fixed i, the pairs (sig[t][i], gv[t][i]) are distinct over t, so the
 * lift is simple and d-regular. Vertices: A fibre i at i*N + x, B fibre j at P*N + j*N + y. */

static int curP, curN;
static int sig[MAXD][MAXP];
static int sinv[MAXD][MAXP];
static int gv[MAXD][MAXP];
static int gi[MAXD][MAXP];

/* True if some row s < lim (s != t) already uses the pair (j, g) from source i. */
static int clash(int t, int lim, int i, int j, int g) {
    for (int s = 0; s < lim; s++)
        if (s != t && sig[s][i] == j && gv[s][i] == g) return 1;
    return 0;
}

static void raw_swap(int t, int i1, int i2) {
    int j1 = sig[t][i1], j2 = sig[t][i2];
    sig[t][i1] = j2;
    sig[t][i2] = j1;
    sinv[t][j1] = i2;
    sinv[t][j2] = i1;
}

static void init_lift(int p, int N) {
    curP = p;
    curN = N;
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1), s = perm[i];
            perm[i] = perm[j];
            perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            sig[t][i] = perm[i];
            sinv[t][perm[i]] = i;
        }
    }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < p; i++) {
            int g = 0, tries = 0;
            do {
                g = rndint(N);
                tries++;
            } while (tries < 1000000 && clash(t, t, i, sig[t][i], g));
            gv[t][i] = g;
            gi[t][i] = ginv(&G, g);
        }
}

/* Orbit-reduced objective: total unreached vertices from the 2p fibre identities, within D. */
static int stamp_arr[MAXN], dist_arr[MAXN], q_arr[MAXN];
static int cur_stamp = 0;

static long orbit_bad(void) {
    int P = curP, N = curN, A = P * N, V = 2 * A;
    long total = 0;
    for (int s = 0; s < 2 * P; s++) {
        int src = s < P ? s * N : A + (s - P) * N;
        int head = 0, tail = 0;
        cur_stamp++;
        stamp_arr[src] = cur_stamp;
        dist_arr[src] = 0;
        q_arr[tail++] = src;
        while (head < tail) {
            int v = q_arr[head++];
            int dv = dist_arr[v];
            if (dv >= D) continue;
            if (v < A) {
                int i = v / N, x = v - i * N;
                for (int t = 0; t < d; t++) {
                    int u = A + sig[t][i] * N + gmul(&G, x, gv[t][i]);
                    if (stamp_arr[u] != cur_stamp) {
                        stamp_arr[u] = cur_stamp;
                        dist_arr[u] = dv + 1;
                        q_arr[tail++] = u;
                    }
                }
            } else {
                int w = v - A, j = w / N, y = w - j * N;
                for (int t = 0; t < d; t++) {
                    int i = sinv[t][j];
                    int u = i * N + gmul(&G, y, gi[t][i]);
                    if (stamp_arr[u] != cur_stamp) {
                        stamp_arr[u] = cur_stamp;
                        dist_arr[u] = dv + 1;
                        q_arr[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static void build_lift(Graph *g) {
    int P = curP, N = curN, A = P * N;
    g->n = 2 * A;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= A; }
    for (int t = 0; t < d; t++)
        for (int i = 0; i < P; i++)
            for (int x = 0; x < N; x++)
                add_edge(g, i * N + x, A + sig[t][i] * N + gmul(&G, x, gv[t][i]));
}

/* Annealing over voltages and destination permutations. Returns the final objective. */
static long anneal(int steps, double until) {
    long bad = orbit_bad();
    double T = T0;
    for (int s = 0; s < steps && bad > 0; s++) {
        if ((s & 63) == 0 && now() > until) break;
        if (curP > 1 && rndint(4) == 0) {
            int t = rndint(d), i1 = rndint(curP), i2 = rndint(curP - 1);
            if (i2 >= i1) i2++;
            int j1 = sig[t][i1], j2 = sig[t][i2];
            if (clash(t, d, i1, j2, gv[t][i1]) || clash(t, d, i2, j1, gv[t][i2])) continue;
            raw_swap(t, i1, i2);
            long nb = orbit_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else raw_swap(t, i1, i2);
        } else {
            int t = rndint(d), i = rndint(curP);
            int ng = rndint(curN);
            if (ng == gv[t][i] || clash(t, d, i, sig[t][i], ng)) continue;
            int og = gv[t][i], oi = gi[t][i];
            gv[t][i] = ng;
            gi[t][i] = ginv(&G, ng);
            long nb = orbit_bad();
            if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) bad = nb;
            else { gv[t][i] = og; gi[t][i] = oi; }
        }
        T *= T_DECAY;
        if (T < T_MIN) T = T_MIN;
    }
    return bad;
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
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    static Graph best, cand;
    if (d < 1 || D < 1 || d > MAXD) { printf("0 0\n"); return 0; }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    if (D >= 2) {
        while (now() < t_end) {
            if (best.n + 1 > moore || best.n + 1 > MAXN) break;
            int r = rndint(100);
            int p = r < 30 ? 1 : r < 50 ? 2 : r < 65 ? 3 : r < 80 ? 4 : r < 90 ? 5 : 6;
            long target = best.n + 1;
            long Nmin = (target + 2L * p - 1) / (2L * p);
            if (Nmin < d) Nmin = d;
            long N = Nmin + (rndint(100) < 50 ? 0 : rndint(4));
            if (2L * p * N > MAXN || 2L * p * N > moore) continue;
            int want = rndint(100) < 60;
            if (!random_group((int)N, want) && !random_group((int)N, 0)) continue;
            init_lift(p, (int)N);
            int steps = STEPS * 2 / (p + 1);
            long bad = anneal(steps, t_end);
            if (bad == 0) {
                build_lift(&cand);
                if (cand.n > best.n && is_valid(&cand)) copy_graph(&best, &cand);
            }
        }
    }
    if (!is_valid(&best)) complete_bipartite(&best);
    print_graph(&best);
    return 0;
}
'''


def _hexagon_incidence(q):
    """Incidence graph of the split Cayley hexagon H(q), q = 2 or 4.

    Order 2(q^6-1)/(q-1), degree q+1, bipartite, diameter 6, so it is valid for D = 6 and D = 7.
    Points: points of the quadric X0X4 + X1X5 + X2X6 = X3^2. Lines: quadric lines whose Grassmann
    coordinates satisfy p12=p34, p54=p32, p20=p35, p65=p30, p01=p36, p46=p31.
    Characteristic 2, so signs are irrelevant. The caller validates the result with lib.is_valid.
    """
    F = lib.GF(q)
    MT, AT = F.mul_table, F.add_table
    pts = []
    for v in itertools.product(range(q), repeat=7):
        if any(v) and next(c for c in v if c) == 1:
            s = AT[AT[MT[v[0], v[4]], MT[v[1], v[5]]], AT[MT[v[2], v[6]], MT[v[3], v[3]]]]
            if s == 0:
                pts.append(tuple(int(c) for c in v))
    N = len(pts)
    index = {v: i for i, v in enumerate(pts)}
    P = np.array(pts, dtype=np.int64)
    lines = set()
    for i in range(N - 1):
        x = P[i]
        Y = P[i + 1:]

        def pp(a, b):
            """Grassmann coordinate p_ab = x_a y_b - x_b y_a, for all y in Y."""
            return AT[MT[x[a], Y[:, b]], MT[x[b], Y[:, a]]]

        # Collinearity on the quadric: polar form B(x, y) = 0 (char 2 has no 2*x3*y3 term).
        s = np.zeros(len(Y), dtype=np.int64)
        for a, b in ((0, 4), (1, 5), (2, 6)):
            s = AT[s, AT[MT[x[a], Y[:, b]], MT[Y[:, a], x[b]]]]
        ok = (s == 0)
        ok &= pp(1, 2) == pp(3, 4)
        ok &= pp(5, 4) == pp(3, 2)
        ok &= pp(2, 0) == pp(3, 5)
        ok &= pp(6, 5) == pp(3, 0)
        ok &= pp(0, 1) == pp(3, 6)
        ok &= pp(4, 6) == pp(3, 1)
        for jj in np.nonzero(ok)[0]:
            y = Y[jj]
            # Points of the line: x, and t*x + y for t in GF(q).
            vecs = [tuple(int(c) for c in x)]
            for t in range(q):
                vecs.append(tuple(int(AT[MT[t, x[k]], y[k]]) for k in range(7)))
            idx = []
            for v in vecs:
                c = next(e for e in v if e)
                inv = F.inv(c)
                idx.append(index[tuple(F.mul(inv, e) for e in v)])
            lines.add(tuple(sorted(idx)))
    lines = sorted(lines)
    edges = [(pt, N + k) for k, L in enumerate(lines) for pt in L]
    return 2 * N, edges


def known_starts(d, D):
    """Algebraic candidates (may be empty); build() keeps only those that pass lib.is_valid."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 6 and d - 1 in (2, 4):
        try:
            out.append(_hexagon_incidence(d - 1))
        except Exception:
            pass
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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    # Engine gets 95% of the case time, minus elapsed time and a 1 s safety margin.
    budget = 0.95 * time_limit - (time.monotonic() - t0) - 1.0
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
