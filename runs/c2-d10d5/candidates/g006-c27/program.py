import itertools
import random
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 4
#define PENALTY 1000.0
#define ITERS 6000L
#define PATIENCE 1500L

static int d, Dd, K, G, M, K2, N;
static int POWR[64];
static uint64_t rs;
static int *nbr = NULL;
static uint8_t *reach = NULL, *cand = NULL, *tmpr = NULL;
static int layer[MAXD][MAXK];
static int S[MAXD][MAXK];
static unsigned char POP[256];

static double now(void) { return (double)clock() / CLOCKS_PER_SEC; }

static uint64_t rnd64(void) {
    rs ^= rs >> 12; rs ^= rs << 25; rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

/* Group Z_M x| Z_K2 with r: element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static int mul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}
static int inv_el(int x) {
    int a = x / K2, b = x % K2;
    int nb = (K2 - b) % K2;
    long long t = ((long long)POWR[nb] * a) % M;
    long long na = (M - t) % M;
    return (int)(na * K2 + nb);
}

static int dupcount(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (layer[l][i] == layer[l2][i] && S[l][i] == S[l2][i]) dup++;
    return dup;
}

/* A-block i (vertices i*G+g) joins B-block p = layer[l][i] (vertices (K+p)*G+h) via g ~ g*s. */
static void set_dart(int l, int i) {
    int p = layer[l][i], s = S[l][i];
    int si = inv_el(s);
    int *row = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (K + p) * G + mul(g, s);
        row[(K + p) * G + g] = i * G + mul(g, si);
    }
}

/* Bitmask per vertex: bit b set when representative vertex b*G is within distance t. */
static long compute_reach(uint8_t *out) {
    memset(out, 0, (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[(size_t)b * G] |= (uint8_t)(1u << b);
    for (int t = 0; t < Dd; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint8_t m = out[v];
            for (int l = 0; l < d; l++) m |= out[nbr[(size_t)l * N + v]];
            tmpr[v] = m;
            if (m != out[v]) changed = 1;
        }
        memcpy(out, tmpr, (size_t)N);
        if (!changed) break;
    }
    long sum = 0;
    for (int v = 0; v < N; v++) sum += POP[out[v]];
    return sum;
}

static double cost_of(long sumpop) {
    return (double)(2L * K * N - sumpop) + PENALTY * (double)dupcount();
}

static int search(double deadline) {
    int full = (1 << (2 * K)) - 1;
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layer[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = layer[l][i]; layer[l][i] = layer[l][j]; layer[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) set_dart(l, i);

    double cost = cost_of(compute_reach(reach));
    double c0 = cost > 1 ? cost : 1;
    double best = cost;
    long last = 0;

    for (long t = 0; t < ITERS; t++) {
        if (cost < 0.5) break;
        if ((t & 15) == 0 && now() > deadline) break;
        if (t - last > PATIENCE) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)ITERS);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* Layer-swap move. */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tv = layer[l][i1]; layer[l][i1] = layer[l][i2]; layer[l][i2] = tv;
            set_dart(l, i1); set_dart(l, i2);
            double c2 = cost_of(compute_reach(cand));
            if (c2 <= cost || rnd01() < exp(-(c2 - cost) / temp)) {
                uint8_t *tp = reach; reach = cand; cand = tp;
                cost = c2;
                if (cost < best) { best = cost; last = t; }
            } else {
                tv = layer[l][i1]; layer[l][i1] = layer[l][i2]; layer[l][i2] = tv;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            long nb = 0;
            for (int v = 0; v < N; v++) if (reach[v] != full) nb++;
            if (nb > 0) {
                long pick = (long)(rnd64() % (uint64_t)nb);
                int u = -1;
                for (int v = 0; v < N; v++) {
                    if (reach[v] != full) {
                        if (pick == 0) { u = v; break; }
                        pick--;
                    }
                }
                int block = u / G;
                l = rndint(d);
                if (block < K) {
                    i = block;
                } else {
                    for (int j = 0; j < K; j++)
                        if (layer[l][j] == block - K) { i = j; break; }
                }
            }
        }
        if (i < 0) { l = rndint(d); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        double c2 = cost_of(compute_reach(cand));
        if (c2 <= cost || rnd01() < exp(-(c2 - cost) / temp)) {
            uint8_t *tp = reach; reach = cand; cand = tp;
            cost = c2;
            if (cost < best) { best = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost < 0.5;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int sample_group(int target, int *om, int *ok2, int *or_) {
    static const int CH[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};
    int nch = (int)(sizeof(CH) / sizeof(CH[0]));
    for (int tr = 0; tr < 200; tr++) {
        int k2 = CH[rndint(nch)];
        int m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        int r;
        if (k2 == 1) {
            r = 1;
        } else if (k2 == 2 && rnd01() < 0.3) {
            r = m - 1;
            if (gcdi(r, m) != 1 || ((long long)r * r) % m != 1 % m) continue;
        } else {
            r = -1;
            for (int q = 0; q < 60; q++) {
                int c = m > 2 ? 2 + rndint(m - 2) : 1;
                if (gcdi(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        *om = m; *ok2 = k2; *or_ = r;
        return 1;
    }
    return 0;
}

static void setup(int k, int m, int k2, int r) {
    K = k; M = m; K2 = k2; G = m * k2; N = 2 * K * G;
    POWR[0] = 1 % M;
    for (int t = 1; t < K2; t++) POWR[t] = (int)((long long)POWR[t - 1] * r % M);
    nbr = realloc(nbr, sizeof(int) * (size_t)d * (size_t)N);
    reach = realloc(reach, (size_t)N);
    cand = realloc(cand, (size_t)N);
    tmpr = realloc(tmpr, (size_t)N);
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: prog d D seed budget best_n\n");
        return 1;
    }
    d = atoi(argv[1]);
    Dd = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int bestN = atoi(argv[5]);

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int x = 0; x < 256; x++) {
        int c = 0, y = x;
        while (y) { c += y & 1; y >>= 1; }
        POP[x] = (unsigned char)c;
    }
    if (d < 2 || d > MAXD || Dd < 2) {
        printf("0 0\n");
        return 0;
    }

    double deadline = now() + budget;
    int *bestA = NULL;
    int bestK = 0, bestG = 0;
    long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};

    while (now() < deadline) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(MAXK);
        } else {
            double bv = -1.0;
            k = 1;
            for (int kk = 1; kk <= MAXK; kk++) {
                double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (v > bv) { bv = v; k = kk; }
            }
        }
        int base = bestN / (2 * k);
        int extra = base / 8 + 1;
        if (extra < 2) extra = 2;
        int target = base + 1 + rndint(extra);
        if (target < 2) target = 2;

        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        setup(k, m, k2, r);
        if (2 * K * G <= bestN) continue;

        trials[k]++;
        if (search(deadline)) {
            wins[k]++;
            bestN = N;
            free(bestA);
            bestA = malloc(sizeof(int) * (size_t)K * G * d);
            for (int u = 0; u < K * G; u++)
                for (int l = 0; l < d; l++)
                    bestA[u * d + l] = nbr[(size_t)l * N + u];
            bestK = K;
            bestG = G;
        }
    }

    if (bestA == NULL) {
        printf("0 0\n");
        return 0;
    }
    int nA = bestK * bestG;
    printf("%d %d\n", bestN, nA * d);
    for (int u = 0; u < nA; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, bestA[u * d + l]);
    free(bestA);
    free(nbr); free(reach); free(cand); free(tmpr);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
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
                for r in L:
                    if p < r:
                        covered.add((p, r))

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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
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
# Main entry point. The bi-Cayley annealing (semidirect-product lifts over
# Z_m x| Z_k2 with k base blocks per side) now runs in the C engine, which is
# roughly 10-100x faster than the numpy version, so many more group/voltage
# restarts fit into the budget.
# ----------------------------------------------------------------------------

def _c_search(d, D, seed, budget, best_n, time_limit):
    """Run the C bi-Cayley search; returns (n, edges) with n == 0 when nothing better was found."""
    raw = lib.run_c(C_SOURCE, [d, D, int(seed) & 0x7FFFFFFF, budget, best_n],
                    stdin_graph=None, timeout=time_limit - 4.0)
    return lib.parse_graph_text(raw)


def build(d, D, seed, time_limit):
    start = time.monotonic()
    final_deadline = start + max(1.0, time_limit - 3.0)
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

    # Exact constructions: return immediately (calibration-style cases).
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < start + 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search in C.
    if d <= 60 and time.monotonic() < final_deadline - 2.0:
        budget = max(1.0, min(0.80 * time_limit, time_limit - 8.0))
        try:
            n2, e2 = _c_search(d, D, seed, budget, best_n, time_limit)
            if n2 > best_n and e2:
                consider(n2, [tuple(e) for e in e2])
        except RuntimeError:
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
