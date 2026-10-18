"""Joint base-graph and voltage annealing for the d=5, D=7 target.

This version replaces the bi-Cayley climb with a different search. Each candidate is a
d-regular bipartite base multigraph on p+p vertices (p = 1..6) with voltages in a random
group Z_m x| Z_k of order N. The lift has 2pN vertices. Annealing moves change the voltages
and also swap the B-endpoints of two base darts, which keeps the base regular and checks
connectivity. The objective is the number of bad (source fibre, vertex) pairs, computed
implicitly from the 2p fibre representatives, since left translation is an automorphism.

Every candidate is verified by a full all-pairs check in C and again in Python with
lib.is_valid. The start graph is the best algebraic graph (hexagon, projective plane or
Araujo-Lopez), or K_{d,d}, so every case returns a valid graph.
"""
import time

import itertools

import numpy as np

import lib

C_SOURCE = r'''
/* Joint base-graph / voltage annealing for bipartite degree-diameter lifts.
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
#define MAXP 6
#define MAXH 2048
#define MAXDART (MAXP * MAXD)

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

typedef struct {
    int m, k, r;
    int rp[MAXH];
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

static void copy_graph(Graph *dst, const Graph *src) {
    dst->n = src->n;
    for (int v = 0; v < src->n; v++) {
        dst->deg[v] = src->deg[v];
        dst->side[v] = src->side[v];
        memcpy(dst->adj[v], src->adj[v], sizeof(int) * src->deg[v]);
    }
}

static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];

/* Exact count of unordered vertex pairs at distance > D (bitset BFS). */
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

/* ---------------- groups: Z_m x|_r Z_k, element a*k+b ---------------- */

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    return (int)((a + (long)G->rp[b] * c) % G->m) * G->k + (b + e) % G->k;
}

/* Uniformly random admissible semidirect product of order N (reservoir sampling). */
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

/* Prefer a non-abelian choice (r != 1, k > 1) when one is sampled quickly. */
static int pick_group(int N, Grp *G) {
    for (int tries = 0; tries < 8; tries++) {
        if (!random_group(N, G)) return 0;
        if (G->m > 1 && G->k > 1 && G->r != 1) return 1;
    }
    return 1;
}

/* ---------------- lift state: p fibres per side, group order N ---------------- */

static int P_, N_, nd_;
static int dart_i[MAXDART], dart_j[MAXDART], dart_g[MAXDART];
static int MTAB[MAXH * MAXH];
static int INV_[MAXH];
static int lst[2 * MAXP][MAXD];
static int seen_st[MAXN], dd_[MAXN], dq_[MAXN];
static int st_ctr = 0;

static void setup_group(const Grp *G, int N) {
    N_ = N;
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MTAB[(size_t)x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MTAB[(size_t)x * N + y] == 0) { INV_[x] = y; break; }
}

/* Each fibre has exactly d darts; list them per fibre. A-fibre i: f = i; B-fibre j: f = p + j. */
static void build_lists(void) {
    int p = P_;
    int cnt[2 * MAXP];
    for (int f = 0; f < 2 * p; f++) cnt[f] = 0;
    for (int t = 0; t < nd_; t++) {
        int f = dart_i[t];
        lst[f][cnt[f]++] = t;
    }
    for (int t = 0; t < nd_; t++) {
        int f = p + dart_j[t];
        lst[f][cnt[f]++] = t;
    }
}

/* Sum over the 2p fibre representatives (identity element) of vertices at distance > D.
 * Zero iff the lift has diameter <= D (left translations are automorphisms). */
static long eval_bad(void) {
    int p = P_, N = N_, V = 2 * p * N;
    build_lists();
    long total = 0;
    for (int src = 0; src < 2 * p; src++) {
        int s = src * N;
        st_ctr++;
        int head = 0, tail = 0;
        seen_st[s] = st_ctr;
        dd_[s] = 0;
        dq_[tail++] = s;
        while (head < tail) {
            int v = dq_[head++];
            int dv = dd_[v];
            if (dv >= D) continue;
            int f = v / N, x = v - f * N;
            const int *row = MTAB + (size_t)x * N;
            if (f < p) {
                for (int k = 0; k < d; k++) {
                    int t = lst[f][k];
                    int u = (p + dart_j[t]) * N + row[dart_g[t]];
                    if (seen_st[u] != st_ctr) {
                        seen_st[u] = st_ctr;
                        dd_[u] = dv + 1;
                        dq_[tail++] = u;
                    }
                }
            } else {
                for (int k = 0; k < d; k++) {
                    int t = lst[f][k];
                    int u = dart_i[t] * N + row[INV_[dart_g[t]]];
                    if (seen_st[u] != st_ctr) {
                        seen_st[u] = st_ctr;
                        dd_[u] = dv + 1;
                        dq_[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static int has_dup(void) {
    for (int a = 0; a < nd_; a++)
        for (int b = a + 1; b < nd_; b++)
            if (dart_i[a] == dart_i[b] && dart_j[a] == dart_j[b] && dart_g[a] == dart_g[b])
                return 1;
    return 0;
}

/* Base multigraph connected? Label propagation over p+p base vertices. */
static int base_connected(int p) {
    int lab[2 * MAXP];
    for (int v = 0; v < 2 * p; v++) lab[v] = v;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int t = 0; t < nd_; t++) {
            int a = dart_i[t], b = p + dart_j[t];
            int m = lab[a] < lab[b] ? lab[a] : lab[b];
            if (lab[a] != m) { lab[a] = m; changed = 1; }
            if (lab[b] != m) { lab[b] = m; changed = 1; }
        }
    }
    for (int v = 0; v < 2 * p; v++)
        if (lab[v] != 0) return 0;
    return 1;
}

static void shuffle_int(int *a, int n) {
    for (int i = n - 1; i > 0; i--) {
        int j = rndint(i + 1);
        int t = a[i];
        a[i] = a[j];
        a[j] = t;
    }
}

/* Random d-regular base on p+p vertices with random voltages in Z_N, no duplicate darts. */
static int init_darts(int p, int N) {
    int js[MAXDART];
    nd_ = p * d;
    for (int t = 0; t < nd_; t++) {
        dart_i[t] = t / d;
        js[t] = t % p;
    }
    for (int tries = 0; tries < 20000; tries++) {
        shuffle_int(js, nd_);
        for (int t = 0; t < nd_; t++) {
            dart_j[t] = js[t];
            dart_g[t] = rndint(N);
        }
        if (!has_dup() && base_connected(p)) return 1;
    }
    return 0;
}

/* One annealing move on the joint (base, voltage) state. Returns 0 if the state is not admissible. */
static int propose(int p) {
    int t = rndint(nd_);
    if (rnd01() < 0.5) {
        dart_g[t] = rndint(N_);
    } else {
        int s = rndint(nd_);
        if (dart_j[s] == dart_j[t]) return 0;
        int tmp = dart_j[t];
        dart_j[t] = dart_j[s];
        dart_j[s] = tmp;
    }
    if (has_dup() || !base_connected(p)) return 0;
    return 1;
}

static void build_full(Graph *g) {
    int p = P_, N = N_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) { g->deg[v] = 0; g->side[v] = v >= p * N; }
    for (int t = 0; t < nd_; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, dart_i[t] * N + x,
                     p * N + dart_j[t] * N + MTAB[(size_t)x * N + dart_g[t]]);
}

/* Anneal the joint state for one (p, group) pair. On success, fill out with a verified graph. */
static int anneal(int p, long steps, double until, Graph *out) {
    if (!init_darts(p, N_)) return 0;
    long E = eval_bad();
    const double T0 = 2.0, T1 = 0.15;
    int sj[MAXDART], sg[MAXDART];
    for (long s = 0; s < steps && E > 0; s++) {
        if ((s & 127) == 0 && now() > until) break;
        double T = T0 * pow(T1 / T0, (double)s / (double)steps);
        memcpy(sj, dart_j, sizeof(int) * nd_);
        memcpy(sg, dart_g, sizeof(int) * nd_);
        if (!propose(p)) {
            memcpy(dart_j, sj, sizeof(int) * nd_);
            memcpy(dart_g, sg, sizeof(int) * nd_);
            continue;
        }
        long NE = eval_bad();
        if (NE <= E || rnd01() < exp((double)(E - NE) / T)) {
            E = NE;
        } else {
            memcpy(dart_j, sj, sizeof(int) * nd_);
            memcpy(dart_g, sg, sizeof(int) * nd_);
        }
    }
    if (E != 0) return 0;
    build_full(out);
    return is_valid(out);
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
    static Grp G;
    if (d < 1 || D < 1 || d > MAXD) {
        complete_bipartite(&best);
        print_graph(&best);
        return 0;
    }
    read_start(&best);
    if (best.n == 0) complete_bipartite(&best);
    if (!is_valid(&best)) complete_bipartite(&best);

    long moore = moore_bound();
    if (d >= 3 && D >= 2) {
        while (now() < t_end && best.n + 2 <= moore) {
            int p = 1 + rndint(MAXP);
            long target = best.n + 2;
            long Nmin = (target + 2L * p - 1) / (2L * p);
            long Nl = Nmin + rndint(4);
            if (Nl < d) Nl = d;
            if (Nl > MAXH) continue;
            int N = (int)Nl;
            if (2L * p * N > moore || 2 * p * N > MAXN) continue;
            if (!pick_group(N, &G)) continue;
            setup_group(&G, N);
            P_ = p;
            if (anneal(p, 20000, t_end, &cand) && cand.n > best.n)
                copy_graph(&best, &cand);
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


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

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.5
    if budget <= 0.5:
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
