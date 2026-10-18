import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley lifts Z_m x| Z_k2 with k base
# blocks per side. Each layer is a perfect matching between A-blocks and
# B-blocks with a group voltage. Reachability is tracked as bitmasks over the
# 2k block representatives, which is exact by vertex transitivity within
# blocks. The C program prints a valid graph on success, else "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXN 200000

static int d, D, k, m, k2, G, N;
static long long rp[64];
static int *nbr;
static uint32_t *cur, *nxt;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static unsigned char pc16[65536];
static uint64_t rs = 88172645463325252ULL;
static const long long PEN = 1000;

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static inline int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + rp[b] * c) % m;
    int bb = (b + e) % k2;
    return (int)(t * k2 + bb);
}

/* A_{i,g} = i*G+g joins B_{p,g*s} = (k+p)*G + gmul(g,s). */
static void set_dart(int l, int i, int p, int s) {
    int *nb = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        int A = i * G + g;
        int B = (k + p) * G + h;
        nb[A] = B;
        nb[B] = A;
    }
}

static void init_random(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < k; i++) S[l][i] = rnd_int(G);
    }
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            set_dart(l, i, layers[l][i], S[l][i]);
}

static long long dupcount(void) {
    long long c = 0;
    int q = d * k;
    for (int a = 0; a < q; a++) {
        int la = a / k, ia = a % k;
        for (int b = 0; b < a; b++) {
            int lb = b / k, ib = b % k;
            if (ia == ib && layers[la][ia] == layers[lb][ib] && S[la][ia] == S[lb][ib])
                c++;
        }
    }
    return c;
}

static long long evalcost(void) {
    int nb2 = 2 * k;
    uint32_t full = (1u << nb2) - 1u;
    memset(cur, 0, sizeof(uint32_t) * (size_t)N);
    for (int b = 0; b < nb2; b++) cur[(size_t)b * G] |= 1u << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[(size_t)l * N + v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint32_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += nb2 - pc16[cur[v] & full];
    return unr + PEN * dupcount();
}

static int run_search(double tend) {
    const int L = 6000, PAT = 1500;
    uint32_t full = (1u << (2 * k)) - 1u;
    while (now_s() < tend) {
        init_random();
        long long cost = evalcost();
        if (cost == 0) return 1;
        long long c0 = cost > 1 ? cost : 1;
        long long best = cost;
        int t_last = 0;
        for (int t = 0; t < L; t++) {
            if (t - t_last > PAT) break;
            if ((t & 31) == 0 && now_s() >= tend) return 0;
            double frac = (double)t / (double)L;
            double temp = 0.01 * (double)c0 * (1.0 - frac);
            if (temp < 0.5) temp = 0.5;

            if (k >= 2 && rnd_unit() < 0.25) {
                int l = rnd_int(d);
                int i1 = rnd_int(k), i2 = rnd_int(k - 1);
                if (i2 >= i1) i2++;
                int tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1, layers[l][i1], S[l][i1]);
                set_dart(l, i2, layers[l][i2], S[l][i2]);
                long long c2 = evalcost();
                if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                    if (cost < best) { best = cost; t_last = t; }
                    if (cost == 0) return 1;
                } else {
                    tmp = layers[l][i1];
                    layers[l][i1] = layers[l][i2];
                    layers[l][i2] = tmp;
                    set_dart(l, i1, layers[l][i1], S[l][i1]);
                    set_dart(l, i2, layers[l][i2], S[l][i2]);
                }
            } else {
                int l = 0, i = 0;
                int u = -1;
                if (rnd_unit() < 0.4) {
                    for (int tries = 0; tries < 64; tries++) {
                        int v = rnd_int(N);
                        if (cur[v] != full) { u = v; break; }
                    }
                }
                if (u >= 0) {
                    int block = u / G;
                    l = rnd_int(d);
                    if (block < k) {
                        i = block;
                    } else {
                        int p = block - k;
                        i = -1;
                        for (int ii = 0; ii < k; ii++)
                            if (layers[l][ii] == p) { i = ii; break; }
                        if (i < 0) i = rnd_int(k);
                    }
                } else {
                    l = rnd_int(d);
                    i = rnd_int(k);
                }
                int old = S[l][i];
                int nw = rnd_int(G);
                if (nw == old) continue;
                S[l][i] = nw;
                set_dart(l, i, layers[l][i], nw);
                long long c2 = evalcost();
                if (c2 <= cost || rnd_unit() < exp(-(double)(c2 - cost) / temp)) {
                    cost = c2;
                    if (cost < best) { best = cost; t_last = t; }
                    if (cost == 0) return 1;
                } else {
                    S[l][i] = old;
                    set_dart(l, i, layers[l][i], old);
                }
            }
        }
    }
    return 0;
}

static void print_graph(void) {
    long long M = (long long)k * G * d;
    printf("%d %lld\n", N, M);
    for (int u = 0; u < k * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
}

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tslice = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    long long r = atoll(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 1 || k2 < 1 || k2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    if ((long long)2 * k * G > MAXN) {
        printf("0 0\n");
        return 0;
    }
    r %= m;
    if (r < 0) r += m;
    rp[0] = 1 % m;
    for (int t = 1; t < k2; t++) rp[t] = rp[t - 1] * r % m;
    if ((rp[k2 - 1] * r) % m != 1 % m) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * k * G;
    nbr = malloc(sizeof(int) * (size_t)d * N);
    cur = malloc(sizeof(uint32_t) * (size_t)N);
    nxt = malloc(sizeof(uint32_t) * (size_t)N);
    if (!nbr || !cur || !nxt) {
        printf("0 0\n");
        return 0;
    }
    pc16[0] = 0;
    for (int x = 1; x < 65536; x++) pc16[x] = (unsigned char)(pc16[x >> 1] + (x & 1));
    rs = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 1ULL;
    if (rs == 0) rs = 1;
    for (int t = 0; t < 10; t++) rnd64();

    int ok = run_search(now_s() + tslice);
    if (ok) print_graph();
    else printf("0 0\n");

    free(nbr);
    free(cur);
    free(nxt);
    return 0;
}
'''

_KS = (1, 2, 3, 4, 5, 6)
_MAX_N = 60000
_SLICE = 5.0


# ----------------------------------------------------------------------------
# Exact and safe constructions (unchanged from the parent).
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
# Group sampling and the bandit driver.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 >= target and r^k2 = 1 mod m, or None."""
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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + max(1.0, min(0.80 * time_limit, time_limit - 10.0))
    final_deadline = t0 + max(1.0, time_limit - 5.0)
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
        if n > best_n:
            try:
                ok = lib.is_valid(n, e, d, D)
            except Exception:
                ok = False
            if ok:
                best = (n, list(e))
                best_n = n

    # Exact constructions: return immediately for the calibration case.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: C annealing on bi-Cayley lifts, driven by a bandit over k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 0.5:
            break
        k = pick_k()
        base = best_n // (2 * k)
        target = max(2, base + 1 + rng.randrange(0, max(2, base // 8 + 1)))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        G = m * k2
        N = 2 * k * G
        if N <= best_n or N > _MAX_N:
            continue
        slice_t = min(_SLICE, deadline - time.monotonic())
        if slice_t < 0.3:
            break
        trials[k] += 1
        try:
            out = lib.run_c(C_SOURCE,
                            [d, D, rng.randrange(1 << 31), f"{slice_t:.3f}", k, m, k2, r],
                            stdin_graph=None, timeout=slice_t + 20.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > 0 and e:
            wins[k] += 1
            consider(n, e)

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline - 2.0:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
