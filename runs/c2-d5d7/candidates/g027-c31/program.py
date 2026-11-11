"""Bold change for the d=5, D=7 target: a multi-fibre voltage-lift search.

The parent searched single-fibre bi-Cayley lifts (2N vertices, one orbit per side) with an
all-pairs check on each candidate. This version searches lifts with p = 2, 3 or 4 fibres per side,
so the order is 2pN. For d=5, D=7 that gives orders 4N, 6N, 8N, which reach 3112 = 4*778 and so
beat the record 3110 = 2*1555 in a different family. The change is:

  * The base is a random connected d-regular bipartite multigraph on p+p fibres, with
    voltages in a non-abelian semidirect product Z_m x| Z_k of order N.
  * Each dart joins A-fibre i to B-fibre j with voltage g, so vertex (i,x) joins (j, x*g).
    Left multiplication by G is an automorphism that is transitive on each fibre, so the
    diameter is at most D iff every fibre representative has eccentricity at most D. The
    objective is the number of unreached vertices from these 2p representatives. Neighbours
    are computed on the fly from the dart lists, so no graph is built per move.
  * Voltages are annealed geometrically (T: 1.5 -> 0.15) with elite restarts. Only when the
    objective reaches zero is the lift built explicitly and checked in C with an all-pairs
    bitset test.
  * The C engine runs for the whole budget. The Python side keeps the best algebraic start
    (PG(2,q), Araujo-Pardo-Lopez, or the split Cayley hexagon H(q)) and validates the C output
    with lib.is_valid before returning it, so every case returns a valid graph.
"""
import itertools
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Multi-fibre voltage-lift search for bipartite degree-diameter graphs.
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
#define MAXP 4
#define MAXH 2048
#define MAXDART (MAXD * MAXP)
#define STEPS 8000
#define SPAN 120
#define ATTEMPTS 4

typedef struct {
    int n;
    int deg[MAXN];
    int adj[MAXN][MAXD];
    unsigned char side[MAXN];
} Graph;

static int d, D;

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
    static int queue[MAXN];
    int n, m;
    g->n = 0;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || n > MAXN) return;
    g->n = n;
    for (int v = 0; v < n; v++) { g->deg[v] = 0; g->side[v] = 255; }
    for (int e = 0; e < m; e++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2 || u < 0 || v < 0 || u >= n || v >= n ||
            u == v || g->deg[u] >= MAXD || g->deg[v] >= MAXD) {
            g->n = 0;
            return;
        }
        add_edge(g, u, v);
    }
    for (int s = 0; s < n; s++) {
        if (g->side[s] != 255) continue;
        int head = 0, tail = 0;
        g->side[s] = 0;
        queue[tail++] = s;
        while (head < tail) {
            int v = queue[head++];
            for (int i = 0; i < g->deg[v]; i++) {
                int u = g->adj[v][i];
                if (g->side[u] == 255) {
                    g->side[u] = (unsigned char)(1 - g->side[v]);
                    queue[tail++] = u;
                } else if (g->side[u] == g->side[v]) {
                    g->n = 0;
                    return;
                }
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

typedef struct {
    int m, k, r;
    int rp[MAXH];
} Grp;

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
            if (rndint((int)count) == 0) {
                G->m = m;
                G->k = k;
                G->r = r;
            }
        }
    }
    if (!count) return 0;
    G->rp[0] = 1 % G->m;
    for (int b = 1; b < G->k; b++)
        G->rp[b] = (int)((long)G->rp[b - 1] * G->r % G->m);
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

static int MT[MAXH * MAXH];
static int INVT[MAXH];

static void setup_group(int N, const Grp *G) {
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            MT[x * N + y] = gmul(G, x, y);
    for (int x = 0; x < N; x++)
        for (int y = 0; y < N; y++)
            if (MT[x * N + y] == 0) { INVT[x] = y; break; }
}

/* ---------------- base multigraph and darts ---------------- */

static int Mb[MAXP][MAXP];
static int nd;
static int di[MAXDART], dj[MAXDART], dg[MAXDART];
static int aList[MAXP][MAXD], bList[MAXP][MAXD];
static int P_, NF;

/* Random d-regular bipartite multigraph on p+p fibres, connected. */
static void make_base(int p) {
    for (;;) {
        memset(Mb, 0, sizeof Mb);
        for (int t = 0; t < d; t++) {
            int perm[MAXP];
            for (int i = 0; i < p; i++) perm[i] = i;
            for (int i = p - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int s = perm[i];
                perm[i] = perm[j];
                perm[j] = s;
            }
            for (int i = 0; i < p; i++) Mb[i][perm[i]]++;
        }
        int seen[2 * MAXP] = {0}, stack[2 * MAXP], top = 0, nseen = 1;
        seen[0] = 1;
        stack[top++] = 0;
        while (top) {
            int v = stack[--top];
            for (int u = 0; u < 2 * p; u++) {
                if (seen[u]) continue;
                int linked = v < p ? (u >= p && Mb[v][u - p]) : (u < p && Mb[u][v - p]);
                if (linked) {
                    seen[u] = 1;
                    nseen++;
                    stack[top++] = u;
                }
            }
        }
        if (nseen == 2 * p) return;
    }
}

static void make_darts(int p) {
    nd = 0;
    for (int i = 0; i < p; i++)
        for (int j = 0; j < p; j++)
            for (int c = 0; c < Mb[i][j]; c++) {
                di[nd] = i;
                dj[nd] = j;
                dg[nd] = -1;
                nd++;
            }
    int ca[MAXP] = {0}, cb[MAXP] = {0};
    for (int t = 0; t < nd; t++) {
        aList[di[t]][ca[di[t]]++] = t;
        bList[dj[t]][cb[dj[t]]++] = t;
    }
}

/* A voltage g is admissible for dart t if no other dart on the same fibre pair has it. */
static int voltage_ok(int t, int g) {
    for (int s = 0; s < nd; s++)
        if (s != t && di[s] == di[t] && dj[s] == dj[t] && dg[s] == g) return 0;
    return 1;
}

/* Fibre f < p is A-fibre f; fibre f >= p is B-fibre f-p. Vertex = fibre*N + element. */
static int mark_s[MAXN], dist_s[MAXN], q_s[MAXN];
static int stamp_s = 0;

/* Sum over the 2p fibre representatives of the number of vertices at distance > D. */
static long orbit_bad(void) {
    int N = NF, V = 2 * P_ * N;
    long total = 0;
    for (int f = 0; f < 2 * P_; f++) {
        int src = f * N;
        stamp_s++;
        int head = 0, tail = 0;
        mark_s[src] = stamp_s;
        dist_s[src] = 0;
        q_s[tail++] = src;
        while (head < tail) {
            int v = q_s[head++];
            int dv = dist_s[v];
            if (dv >= D) continue;
            int fv = v / N, x = v - fv * N;
            if (fv < P_) {
                const int *al = aList[fv];
                for (int k = 0; k < d; k++) {
                    int t = al[k];
                    int u = (P_ + dj[t]) * N + MT[x * N + dg[t]];
                    if (mark_s[u] != stamp_s) {
                        mark_s[u] = stamp_s;
                        dist_s[u] = dv + 1;
                        q_s[tail++] = u;
                    }
                }
            } else {
                const int *bl = bList[fv - P_];
                for (int k = 0; k < d; k++) {
                    int t = bl[k];
                    int u = di[t] * N + MT[x * N + INVT[dg[t]]];
                    if (mark_s[u] != stamp_s) {
                        mark_s[u] = stamp_s;
                        dist_s[u] = dv + 1;
                        q_s[tail++] = u;
                    }
                }
            }
        }
        total += V - tail;
    }
    return total;
}

static void build_lift(Graph *g) {
    int N = NF, p = P_;
    g->n = 2 * p * N;
    for (int v = 0; v < g->n; v++) {
        g->deg[v] = 0;
        g->side[v] = (unsigned char)(v >= p * N);
    }
    for (int t = 0; t < nd; t++)
        for (int x = 0; x < N; x++)
            add_edge(g, di[t] * N + x, (p + dj[t]) * N + MT[x * N + dg[t]]);
}

static int BG[MAXDART];

/* Geometric-cooling anneal over the voltages. Returns the best objective; BG holds its voltages. */
static long anneal(double until) {
    long bad = orbit_bad();
    long bestb = bad;
    memcpy(BG, dg, sizeof(int) * nd);
    double T = 1.5;
    const double alpha = pow(0.1, 1.0 / STEPS);
    for (int s = 0; s < STEPS && bad > 0; s++) {
        if ((s & 15) == 0 && now() > until) break;
        int t = rndint(nd), old = dg[t], g;
        do { g = rndint(NF); } while (!voltage_ok(t, g));
        dg[t] = g;
        long nb = orbit_bad();
        if (nb <= bad || rnd01() < exp((double)(bad - nb) / T)) {
            bad = nb;
            if (bad < bestb) {
                bestb = bad;
                memcpy(BG, dg, sizeof(int) * nd);
            }
        } else {
            dg[t] = old;
        }
        T *= alpha;
    }
    return bestb;
}

/* Feasible lift range for p fibres: 2pN > L, 2pN <= min(MAXN, moore), N <= MAXH. */
static int feasible_p(int p, long L, long moore, int *lo_out, int *hi_out) {
    long lo = L / (2 * p) + 1;
    if (lo < d + 1) lo = d + 1;
    long hi = MAXH;
    if (hi > MAXN / (2 * p)) hi = MAXN / (2 * p);
    if (hi > moore / (2 * p)) hi = moore / (2 * p);
    *lo_out = (int)lo;
    *hi_out = (int)hi;
    return lo <= hi;
}

static void lift_search(Graph *best, double until) {
    static Grp G;
    static Graph cand;
    static int elite[MAXDART];
    while (now() < until) {
        long L = best->n, moore = moore_bound();
        int ps[3], np = 0;
        for (int p = 2; p <= 4; p++) {
            int lo, hi;
            if (feasible_p(p, L, moore, &lo, &hi)) ps[np++] = p;
        }
        if (np == 0) return;
        int p = ps[rndint(np)];
        int lo, hi;
        feasible_p(p, L, moore, &lo, &hi);
        int span = hi - lo + 1;
        if (span > SPAN) span = SPAN;
        /* Bias toward the lowest open orders, which are likeliest to succeed. */
        double u = rnd01();
        int N = lo + (int)(u * sqrt(u) * span);
        if (N > hi) N = hi;
        if (!pick_group(N, &G)) continue;
        setup_group(N, &G);
        P_ = p;
        NF = N;
        make_base(p);
        make_darts(p);

        long elite_bad = -1;
        for (int att = 0; att < ATTEMPTS && now() < until; att++) {
            if (elite_bad >= 0 && rnd01() < 0.6) {
                memcpy(dg, elite, sizeof(int) * nd);
                int t = rndint(nd), g;
                do { g = rndint(NF); } while (!voltage_ok(t, g));
                dg[t] = g;
            } else {
                for (int t = 0; t < nd; t++) dg[t] = -1;
                for (int t = 0; t < nd; t++) {
                    int g;
                    do { g = rndint(NF); } while (!voltage_ok(t, g));
                    dg[t] = g;
                }
            }
            long b = anneal(until);
            if (b == 0) {
                memcpy(dg, BG, sizeof(int) * nd);
                build_lift(&cand);
                if (cand.n > best->n && is_valid(&cand)) {
                    copy_graph(best, &cand);
                    break;
                }
            } else if (elite_bad < 0 || b < elite_bad) {
                elite_bad = b;
                memcpy(elite, BG, sizeof(int) * nd);
            }
        }
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
    double t_end = t0 + limit * 0.93;
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
    if (!is_valid(&best)) complete_bipartite(&best);

    if (D >= 2 && d >= 3 && best.n < moore_bound()) lift_search(&best, t_end);

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

    best = lib.haar_graph(d, range(d))  # K_{d,d}: valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if d > 31 or best[0] >= lib.moore_bound(d, D):
        return best

    budget = 0.9 * time_limit - (time.monotonic() - t0) - 1.0
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
