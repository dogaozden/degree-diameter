import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift annealer over Z_m x| Z_k2 with iterated local search.
#
# Vertices: A_{i,g} = i*G + g (i < K), B_{j,h} = (K+j)*G + h, G = M*K2.
# Layer l pairs A_i with B_{layers[l][i]} through voltage S[l][i]: A_{i,g} ~ B_{j,g*s}.
# Every layer is a permutation, so every vertex has degree d.
# Cost = unreached (block representative, vertex) pairs + PEN * duplicate darts.
# New in this version: the whole annealing loop runs in C (about 20-50x faster than
# the numpy version), restarts from a fresh random state when a run stagnates, and
# the outer loop in Python chooses group orders and budgets per trial.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

#define MAXD 64
#define MAXK 4
#define MAXK2 64
#define PEN 1000
#define KICK 3
#define EPOCH 20000L
#define PATIENCE 3000L
#define MAXRESTART 4

typedef uint64_t u64;

static int d, Dd, K, G, M, K2, R, N;
static int PW[MAXK2];
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static int bestL[MAXD][MAXK];
static int bestS[MAXD][MAXK];
static int *nbr;
static u64 *curR, *tmpR, *scr;
static u64 rs = 88172645463325252ULL;
static u64 FULLM;

static double now_sec(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static u64 rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd64() % (u64)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static int pc64(u64 x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

/* (a,b)*(c,e) = (a + r^b c, b + e) with element code a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + (long long)PW[b] * (long long)c) % M;
    return (int)t * K2 + (b + e) % K2;
}

static void set_dart(int l, int i, int j, int s) {
    int *row = nbr + (size_t)l * (size_t)N;
    int bi = i * G, bj = (K + j) * G;
    for (int g = 0; g < G; g++) {
        int h = gmul(g, s);
        row[bi + g] = bj + h;
        row[bj + h] = bi + g;
    }
}

static void rebuild_all(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i, layers[l][i], S[l][i]);
}

static int dupcount(void) {
    int dup = 0;
    int total = d * K;
    for (int a = 0; a < total; a++) {
        int la = a / K, ia = a % K;
        for (int b = 0; b < a; b++) {
            int lb = b / K, ib = b % K;
            if (ia == ib && layers[la][ia] == layers[lb][ib] && S[la][ia] == S[lb][ib])
                dup++;
        }
    }
    return dup;
}

/* out[v] = bitmask of representative blocks within distance Dd of v. */
static void compute_reach(u64 *out, u64 *buf) {
    memset(out, 0, sizeof(u64) * (size_t)N);
    for (int b = 0; b < 2 * K; b++) out[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < Dd; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            u64 x = out[v];
            for (int l = 0; l < d; l++) x |= out[nbr[(size_t)l * N + v]];
            buf[v] = x;
            if (x != out[v]) changed = 1;
        }
        memcpy(out, buf, sizeof(u64) * (size_t)N);
        if (!changed) break;
    }
}

static int full_cost(u64 *out, u64 *buf) {
    compute_reach(out, buf);
    long long unr = 0;
    for (int v = 0; v < N; v++) unr += 2 * K - pc64(out[v]);
    return (int)(unr + (long long)PEN * dupcount());
}

static void init_random(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) layers[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = tmp;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
}

static void save_best(void) {
    memcpy(bestL, layers, sizeof layers);
    memcpy(bestS, S, sizeof S);
}

static void restore_best(void) {
    memcpy(layers, bestL, sizeof layers);
    memcpy(S, bestS, sizeof S);
}

/* One annealing run from a random start with ILS kicks. Returns 1 if cost 0 found. */
static int search(double deadline) {
    init_random();
    rebuild_all();
    int cost = full_cost(curR, scr);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best_cost = cost;
    save_best();
    long last = 0;
    int restarts = 0;

    for (long t = 0; ; t++) {
        if (cost == 0) break;
        if ((t & 127) == 0 && now_sec() > deadline) break;

        if (t - last > PATIENCE) {
            restarts++;
            if (restarts > MAXRESTART) break;
            restore_best();
            rebuild_all();
            for (int q = 0; q < KICK; q++) {
                int l = rndint(d), i = rndint(K);
                S[l][i] = rndint(G);
                set_dart(l, i, layers[l][i], S[l][i]);
            }
            cost = full_cost(curR, scr);
            last = t;
            continue;
        }

        double temp = 0.01 * c0 * (1.0 - (double)(t % EPOCH) / (double)EPOCH);
        if (temp < 0.5) temp = 0.5;
        double x = rnd01();

        if (K >= 2 && x < 0.25) {
            /* Layer-swap move: exchange B-targets of two A-blocks in one layer. */
            int l = rndint(d);
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(l, i1, layers[l][i1], S[l][i1]);
            set_dart(l, i2, layers[l][i2], S[l][i2]);
            int c2 = full_cost(tmpR, scr);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                u64 *p = curR; curR = tmpR; tmpR = p;
                if (cost < best_cost) { best_cost = cost; last = t; save_best(); }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(l, i1, layers[l][i1], S[l][i1]);
                set_dart(l, i2, layers[l][i2], S[l][i2]);
            }
            continue;
        }

        /* Voltage move: defect-targeted with prob 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int u = -1;
            for (int tries = 0; tries < 64; tries++) {
                int v = rndint(N);
                if (curR[v] != FULLM) { u = v; break; }
            }
            if (u >= 0) {
                int block = u / G;
                l = rndint(d);
                if (block < K) {
                    i = block;
                } else {
                    i = -1;
                    for (int ii = 0; ii < K; ii++)
                        if (layers[l][ii] == block - K) { i = ii; break; }
                    if (i < 0) i = rndint(K);
                }
            }
        }
        if (l < 0) { l = rndint(d); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i, layers[l][i], nw);
        int c2 = full_cost(tmpR, scr);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            u64 *p = curR; curR = tmpR; tmpR = p;
            if (cost < best_cost) { best_cost = cost; last = t; save_best(); }
        } else {
            S[l][i] = old;
            set_dart(l, i, layers[l][i], old);
        }
    }
    return cost == 0;
}

static void emit(void) {
    long long m = (long long)K * G * d;
    printf("%d %lld\n", N, m);
    for (int u = 0; u < K * G; u++)
        for (int l = 0; l < d; l++)
            printf("%d %d\n", u, nbr[(size_t)l * N + u]);
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    Dd = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    K = atoi(argv[5]);
    M = atoi(argv[6]);
    K2 = atoi(argv[7]);
    R = atoi(argv[8]);
    if (d < 1 || d > MAXD || Dd < 1 || K < 1 || K > MAXK || M < 2 ||
        K2 < 1 || K2 > MAXK2 || R < 0) {
        printf("0 0\n");
        return 0;
    }
    G = M * K2;
    N = 2 * K * G;
    FULLM = (1ULL << (2 * K)) - 1;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 8; w++) rnd64();

    PW[0] = 1 % M;
    for (int b = 1; b < K2; b++) PW[b] = (int)((long long)PW[b - 1] * R % M);

    nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
    curR = malloc(sizeof(u64) * (size_t)N);
    tmpR = malloc(sizeof(u64) * (size_t)N);
    scr = malloc(sizeof(u64) * (size_t)N);
    if (!nbr || !curR || !tmpR || !scr) { printf("0 0\n"); return 0; }

    double deadline = now_sec() + tl;
    int ok = 0;
    while (!ok && now_sec() < deadline) ok = search(deadline);
    if (ok) emit(); else printf("0 0\n");
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Group sampling and the C search wrapper.
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


def _c_search(d, D, seed, budget, k, m, k2, r):
    """Run the C annealer for one group configuration. Returns (n, edges) or None."""
    try:
        out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", k, m, k2, r],
                        timeout=budget + 8.0)
        n, edges = lib.parse_graph_text(out)
    except (RuntimeError, ValueError, OSError):
        return None
    if n <= 0 or not edges:
        return None
    return n, edges


# ----------------------------------------------------------------------------
# Build.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
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

    # Exact constructions: return immediately for calibration-style cases.
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

    # Main search: C annealer driven by a bandit over base sizes k.
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}
    jump = 0.2  # relative growth of the target order; shrinks after failures

    def pick_k():
        if rng.random() < 0.2:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.02 * rng.random())

    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        k = pick_k()
        base = max(1, best_n // (2 * k))
        target = max(2, base + 1 + int(base * jump * rng.random()))
        g = _sample_group(target, rng)
        if g is None:
            continue
        m, k2, r = g
        if 2 * k * m * k2 <= best_n:
            continue
        slice_ = min(remaining, 6.0)
        trials[k] += 1
        res = _c_search(d, D, rng.randrange(1 << 30), slice_, k, m, k2, r)
        if res is not None:
            wins[k] += 1
            consider(res[0], res[1])
        else:
            jump = max(0.02, jump * 0.85)

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
