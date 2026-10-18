"""Bold variant: bi-Cayley seed search, then a vertex-growing annealer in C.

Phase 1 runs the bi-Cayley voltage annealer (C) to get a strong d-regular valid
seed. Phase 2 is a different search: it starts from that seed and repeatedly
adds two vertices (one A-side, one B-side) by splicing them into d existing
edges. Degrees are preserved, and the graph is repaired with degree-preserving
double edge swaps, using a bitset diameter cost. A snapshot of the last valid
graph is kept, and the search rolls back to it when repair stalls. Every
returned graph is checked with lib.is_valid, and K_{d,d} is the fallback.

Honest caveat: beating the 4000 record needs far more repair throughput than a
60 s budget allows. This is an experiment, and the fallback path guarantees a
valid output either way.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 8
#define PEN 1000L

static int d, D, k, m, k2, r, G, N;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr;
static uint16_t *bufA, *bufB, *resbuf, *accreach;
static int powr[64];
static unsigned char pop16[65536];
static uint64_t RS = 88172645463325252ULL;

static uint64_t rnd64(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

/* Group element x = a*k2 + b, (a,b)(c,e) = (a + r^b c mod m, b + e mod k2). */
static int gmul(int x, int y) {
    int a = x / k2, b = x % k2;
    int c = y / k2, e = y % k2;
    long long t = (long long)a + (long long)powr[b] * c;
    int aa = (int)(t % m);
    int bb = b + e;
    if (bb >= k2) bb -= k2;
    return aa * k2 + bb;
}

/* Dart (l, i): A-block i (vertices i*G+g) joins B-block layers[l][i] at g*S[l][i]. */
static void set_dart(int l, int i) {
    int j = layers[l][i], s = S[l][i];
    for (int g = 0; g < G; g++) {
        int u = i * G + g;
        int w = (k + j) * G + gmul(g, s);
        nbr[(size_t)u * d + l] = w;
        nbr[(size_t)w * d + l] = u;
    }
}

/* Count (vertex, block) pairs at distance > D from a block representative. */
static long eval_cost(void) {
    int NB = 2 * k;
    uint16_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint16_t) * (size_t)N);
    for (int b = 0; b < NB; b++) cur[(size_t)b * G] = (uint16_t)(1u << b);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint16_t x = cur[v];
            const int *nv = nbr + (size_t)v * d;
            for (int l = 0; l < d; l++) x |= cur[nv[l]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint16_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long unreached = 0;
    for (int v = 0; v < N; v++) unreached += NB - pop16[cur[v]];
    memcpy(resbuf, cur, sizeof(uint16_t) * (size_t)N);
    return unreached;
}

static long dupcount(void) {
    long c = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (layers[l1][i] == layers[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static int search(long iters, long patience, double tend) {
    int NB = 2 * k;
    uint16_t full = (uint16_t)((1u << NB) - 1u);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rndint(G);
        for (int i = 0; i < k; i++) set_dart(l, i);
    }
    long cost = eval_cost() + PEN * dupcount();
    memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
    double c0 = (double)(cost > 1 ? cost : 1);
    long best = cost, last = 0;

    for (long t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if ((t & 31) == 0 && now_s() > tend) return 0;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k);
            int i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost() + PEN * dupcount();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
                if (cost < best) { best = cost; last = t; }
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = rndint(d);
        int i = rndint(k);
        if (rnd01() < 0.4) {
            int nb = 0, pick = -1;
            for (int v = 0; v < N; v++) {
                if (accreach[v] != full) {
                    nb++;
                    if (rndint(nb) == 0) pick = v;
                }
            }
            if (pick >= 0) {
                int block = pick / G;
                if (block < k) {
                    i = block;
                } else {
                    int j = block - k;
                    for (int q = 0; q < k; q++)
                        if (layers[l][q] == j) { i = q; break; }
                }
            }
        }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = eval_cost() + PEN * dupcount();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(accreach, resbuf, sizeof(uint16_t) * (size_t)N);
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    k2 = atoi(argv[5]);
    r = atoi(argv[6]);
    unsigned long long seed = strtoull(argv[7], NULL, 10);
    double tl = atof(argv[8]);
    long iters = argc > 9 ? atol(argv[9]) : 20000;
    long patience = argc > 10 ? atol(argv[10]) : 4000;

    if (d < 1 || d > MAXD || k < 1 || k > MAXK || D < 1 || m < 1 || k2 < 1 || k2 > 63) {
        printf("0 0\n");
        return 0;
    }
    if (m > 100000 || (long long)m * k2 > 200000LL) { printf("0 0\n"); return 0; }
    if (r < 0) { printf("0 0\n"); return 0; }
    r %= m;
    G = m * k2;
    N = 2 * k * G;
    powr[0] = 1 % m;
    for (int b = 1; b < k2; b++) powr[b] = (int)((long long)powr[b - 1] * r % m);
    if (((long long)powr[k2 - 1] * r) % m != (1 % m)) { printf("0 0\n"); return 0; }

    for (int x = 1; x < 65536; x++) pop16[x] = (unsigned char)(pop16[x >> 1] + (x & 1));
    nbr = malloc(sizeof(int) * (size_t)N * (size_t)d);
    bufA = malloc(sizeof(uint16_t) * (size_t)N);
    bufB = malloc(sizeof(uint16_t) * (size_t)N);
    resbuf = malloc(sizeof(uint16_t) * (size_t)N);
    accreach = malloc(sizeof(uint16_t) * (size_t)N);
    if (!nbr || !bufA || !bufB || !resbuf || !accreach) { printf("0 0\n"); return 0; }

    RS = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (RS == 0) RS = 88172645463325252ULL;
    for (int w = 0; w < 10; w++) rnd64();

    double tend = now_s() + tl;
    int found = 0;
    while (now_s() < tend) {
        if (search(iters, patience, tend)) { found = 1; break; }
    }
    if (!found) { printf("0 0\n"); return 0; }

    int A = k * G;
    printf("%d %ld\n", N, (long)A * d);
    for (int u = 0; u < A; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)u * d + l]);
    return 0;
}
'''


GROW_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXDEG 64
#define PATIENCE 200L

static int d, D, N, NCAP, WCAP;
static int *adj, *deg, *side;
static int *badj, *bdeg, *bside;
static int bestN = 0, have_best = 0;
static uint64_t *RA, *RB;
static uint64_t RS = 88172645463325252ULL;
static int ma, mb, mc, me;

static uint64_t rnd64(void) {
    RS ^= RS << 13;
    RS ^= RS >> 7;
    RS ^= RS << 17;
    return RS;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < deg[a]; i++)
        if (adj[a * d + i] == b) return 1;
    return 0;
}

static void add_half(int a, int b) {
    adj[a * d + deg[a]] = b;
    deg[a]++;
}

static void del_half(int a, int b) {
    for (int i = 0; i < deg[a]; i++) {
        if (adj[a * d + i] == b) {
            adj[a * d + i] = adj[a * d + deg[a] - 1];
            deg[a]--;
            return;
        }
    }
}

static void add_edge(int a, int b) { add_half(a, b); add_half(b, a); }
static void del_edge(int a, int b) { del_half(a, b); del_half(b, a); }

static int pick(int s) {
    for (int t = 0; t < 1000; t++) {
        int v = rndint(N);
        if (side[v] == s && deg[v] > 0) return v;
    }
    return -1;
}

/* Number of unordered vertex pairs at distance > D. */
static long eval_cost(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t *out = nxt + (size_t)v * W;
            const uint64_t *in = cur + (size_t)v * W;
            memcpy(out, in, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < deg[v]; i++) {
                const uint64_t *nb = cur + (size_t)adj[v * d + i] * W;
                for (int w = 0; w < W; w++) out[w] |= nb[w];
            }
            if (memcmp(out, in, sizeof(uint64_t) * (size_t)W) != 0) changed = 1;
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
        if (!changed) break;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *r = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc64(r[w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Degree-preserving double edge swap: (a,b),(c,e) -> (a,e),(c,b). */
static int swap_move(void) {
    int a = pick(0), c = pick(0);
    if (a < 0 || c < 0 || a == c) return 0;
    int b = adj[a * d + rndint(deg[a])];
    int e = adj[c * d + rndint(deg[c])];
    if (b == e) return 0;
    if (has_edge(a, e) || has_edge(c, b)) return 0;
    del_edge(a, b);
    del_edge(c, e);
    add_edge(a, e);
    add_edge(c, b);
    ma = a; mb = b; mc = c; me = e;
    return 1;
}

static void undo_swap(void) {
    del_edge(ma, me);
    del_edge(mc, mb);
    add_edge(ma, mb);
    add_edge(mc, me);
}

/* Splice d edges (a_i,b_i) into a new A-vertex w ~ all b_i and a new B-vertex z ~ all a_i.
   Every old vertex keeps its degree; w and z get degree d. */
static int grow_move(void) {
    if (N + 2 > NCAP) return 0;
    int as[MAXDEG], bs[MAXDEG];
    int cnt = 0;
    for (int tries = 0; tries < 300 && cnt < d; tries++) {
        int a = pick(0);
        if (a < 0) return 0;
        int b = adj[a * d + rndint(deg[a])];
        int ok = 1;
        for (int i = 0; i < cnt; i++)
            if (as[i] == a || bs[i] == b) { ok = 0; break; }
        if (ok) { as[cnt] = a; bs[cnt] = b; cnt++; }
    }
    if (cnt < d) return 0;
    int w = N, z = N + 1;
    side[w] = 0;
    side[z] = 1;
    deg[w] = 0;
    deg[z] = 0;
    for (int i = 0; i < d; i++) del_edge(as[i], bs[i]);
    for (int i = 0; i < d; i++) {
        add_edge(w, bs[i]);
        add_edge(z, as[i]);
    }
    N += 2;
    return 1;
}

static void save_best(void) {
    memcpy(badj, adj, sizeof(int) * (size_t)N * d);
    memcpy(bdeg, deg, sizeof(int) * (size_t)N);
    memcpy(bside, side, sizeof(int) * (size_t)N);
    bestN = N;
    have_best = 1;
}

static void restore_best(void) {
    memcpy(adj, badj, sizeof(int) * (size_t)bestN * d);
    memcpy(deg, bdeg, sizeof(int) * (size_t)bestN);
    memcpy(side, bside, sizeof(int) * (size_t)bestN);
    N = bestN;
}

static int color_graph(int n, int *q) {
    for (int v = 0; v < n; v++) side[v] = -1;
    for (int s = 0; s < n; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int head = 0, tail = 0;
        q[tail++] = s;
        while (head < tail) {
            int u = q[head++];
            for (int i = 0; i < deg[u]; i++) {
                int v = adj[u * d + i];
                if (side[v] == -1) {
                    side[v] = 1 - side[u];
                    q[tail++] = v;
                } else if (side[v] == side[u]) {
                    return 0;
                }
            }
        }
    }
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    if (d < 1 || d > MAXDEG || D < 1) { printf("0 0\n"); return 0; }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 <= 0 || m0 < 0) { printf("0 0\n"); return 0; }
    NCAP = n0 + 1200;
    WCAP = (NCAP + 63) / 64;
    adj = malloc(sizeof(int) * (size_t)NCAP * d);
    deg = calloc((size_t)NCAP, sizeof(int));
    side = malloc(sizeof(int) * (size_t)NCAP);
    badj = malloc(sizeof(int) * (size_t)NCAP * d);
    bdeg = malloc(sizeof(int) * (size_t)NCAP);
    bside = malloc(sizeof(int) * (size_t)NCAP);
    RA = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    RB = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    int *q = malloc(sizeof(int) * (size_t)NCAP);
    if (!adj || !deg || !side || !badj || !bdeg || !bside || !RA || !RB || !q) {
        printf("0 0\n");
        return 0;
    }

    N = n0;
    for (int i = 0; i < m0; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) break;
        if (u < 0 || v < 0 || u >= N || v >= N || u == v) continue;
        if (has_edge(u, v)) continue;
        if (deg[u] >= d || deg[v] >= d) { printf("0 0\n"); return 0; }
        add_edge(u, v);
    }
    if (!color_graph(N, q)) { printf("0 0\n"); return 0; }

    RS = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (RS == 0) RS = 88172645463325252ULL;
    for (int w = 0; w < 10; w++) rnd64();

    double tend = now_s() + tl;
    long cost = eval_cost();
    long stale = 0, iter = 0;

    while (1) {
        if ((iter++ & 7) == 0 && now_s() > tend) break;

        if (cost == 0) {
            save_best();
            stale = 0;
            if (!grow_move()) {
                if (N + 2 > NCAP) break;
                continue;
            }
            cost = eval_cost();
            continue;
        }

        if (!swap_move()) continue;
        long c2 = eval_cost();
        double T = 0.3 + 0.01 * (double)cost;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            undo_swap();
        }
        stale++;
        if (stale > PATIENCE && have_best) {
            restore_best();
            cost = eval_cost();
            stale = 0;
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    long E = 0;
    for (int v = 0; v < bestN; v++)
        if (bside[v] == 0) E += bdeg[v];
    printf("%d %ld\n", bestN, E);
    for (int v = 0; v < bestN; v++) {
        if (bside[v] != 0) continue;
        for (int i = 0; i < bdeg[v]; i++)
            printf("%d %d\n", v, badj[v * d + i]);
    }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact constructions (fallbacks and seeds).
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _gq_w(q):
    """Incidence graph of points and lines of the generalized quadrangle W(q); diameter 4."""
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
                for r_ in L:
                    if p < r_:
                        covered.add((p, r_))

    edges = []
    for j, L in enumerate(lines):
        for p in L:
            edges.append((p, P + j))
    return 2 * P, edges


def _best_gq(d):
    """W(q) for the largest prime power q with q + 1 <= d, restricted to small q for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Slack extension: add new vertices using spare degree, accepting only valid graphs.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Bi-Cayley seed search (C engine, phase 1).
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        if k2 == 1:
            r = 1
        elif k2 == 2 and rng.random() < 0.3:
            r = m - 1
            if math.gcd(r, m) != 1 or pow(r, 2, m) != 1 % m:
                continue
        else:
            r = None
            for _ in range(60):
                c = rng.randrange(2, m) if m > 2 else 1
                if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m:
                    r = c
                    break
            if r is None:
                continue
        return m, k2, r
    return None


def _c_search(d, D, k, m, k2, r, seed, slice_s):
    """Run the bi-Cayley C annealer for about slice_s seconds. Returns (n, edges) or None."""
    out = lib.run_c(C_SOURCE, [d, D, k, m, k2, r, seed, round(slice_s, 3), 20000, 4000],
                    stdin_graph=None, timeout=slice_s + 8.0)
    n, edges = lib.parse_graph_text(out)
    if n <= 0 or not edges:
        return None
    return n, edges


def _grow_search(d, D, graph, seed, slice_s):
    """Run the vertex-growing annealer starting from a valid graph. Returns (n, edges)."""
    out = lib.run_c(GROW_SOURCE, [d, D, seed, round(slice_s, 3)],
                    stdin_graph=graph, timeout=slice_s + 6.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    total = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    end = start + total
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Phase 1: bi-Cayley seed search (C), about 45% of the budget.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    p1_end = start + 0.45 * total
    c_ok = True
    while c_ok and time.monotonic() < p1_end:
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            continue
        trials[k] += 1
        remaining = p1_end - time.monotonic()
        slice_s = min(remaining, max(1.5, total / 12.0))
        if slice_s < 0.5:
            break
        try:
            res = _c_search(d, D, k, m, k2, r, rng.randrange(1 << 30), slice_s)
        except (RuntimeError, ValueError, OSError):
            c_ok = False
            break
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])

    # Phase 2: vertex-growing annealer from the best valid graph (C).
    if best_n >= 2 and time.monotonic() < end - 3.0:
        slice_s = end - 1.5 - time.monotonic()
        try:
            n2, e2 = _grow_search(d, D, best, rng.randrange(1 << 30), slice_s)
            consider(n2, e2)
        except (RuntimeError, ValueError, OSError):
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < end:
        n3, e3 = _slack_extend(best[0], best[1], d, D, rng, end)
        consider(n3, e3)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
