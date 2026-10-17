import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: multi-start simulated annealing over bi-Cayley lifts of
# Z_m x| Z_k2 (semidirect products), with k base vertices per side.
#
# Vertices: A_{i,g} = i*G + g, B_{j,h} = (k+j)*G + h, G = m*k2.
# Layer l joins A_{i,g} to B_{layers[l][i], g*s[l][i]}. Each layer is a
# permutation, so every vertex has degree d. Left multiplication by G is an
# automorphism, so diameter <= D reduces to: every vertex is within D of each
# of the 2k block representatives. Bitmasks track this.
#
# argv: d D seed seconds best_n kmax
# Searches for a valid graph with more than best_n vertices, climbing as it
# succeeds. Prints the best found as "n m" plus edges, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 64
#define MAXK 16
#define PEN 1000

typedef uint64_t u64;

static u64 rs = 88172645463325252ULL;

static u64 rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) {
    if (n <= 1) return 0;
    return (int)(rnd() % (u64)n);
}

static double rdbl(void) {
    return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0);
}

static int pc(u64 x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static int gcd_(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int dd, DD, kk, mm, k2, rr, GG, NN;
static int *pw = NULL, *ginv = NULL;
static int *nbr = NULL;
static u64 *bufA = NULL, *bufB = NULL, *accr = NULL, *cur = NULL;
static u64 FULL;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = ((long long)a + (long long)pw[b] * c) % mm;
    return (int)(t * k2 + (b + e) % k2);
}

static void setup_group(int m, int k, int r) {
    mm = m;
    k2 = k;
    rr = r;
    GG = m * k;
    pw = malloc(sizeof(int) * (size_t)k);
    pw[0] = 1 % m;
    for (int b = 1; b < k; b++) pw[b] = (int)((long long)pw[b - 1] * r % m);
    ginv = malloc(sizeof(int) * (size_t)GG);
    for (int x = 0; x < GG; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        long long na = (m - ((long long)pw[nb] * a) % m) % m;
        ginv[x] = (int)(na * k + nb);
    }
}

static void free_group(void) {
    free(pw);
    free(ginv);
    pw = NULL;
    ginv = NULL;
}

static void set_dart(int l, int i, int j, int s) {
    int *nl = nbr + (size_t)l * NN;
    int is = ginv[s];
    for (int g = 0; g < GG; g++) {
        nl[i * GG + g] = (kk + j) * GG + gmul(g, s);
        nl[(kk + j) * GG + g] = i * GG + gmul(g, is);
    }
}

/* Returns the number of unreached (representative, vertex) pairs; result in cur. */
static int reach_count(int D) {
    int bits = 2 * kk;
    u64 *x = bufA, *y = bufB;
    for (int v = 0; v < NN; v++) x[v] = 0;
    for (int b = 0; b < bits; b++) x[(size_t)b * GG] = 1ULL << b;
    for (int t = 0; t < D; t++) {
        int changed = 0;
        for (int v = 0; v < NN; v++) {
            u64 acc = x[v];
            for (int l = 0; l < dd; l++) acc |= x[nbr[(size_t)l * NN + v]];
            y[v] = acc;
            if (acc != x[v]) changed = 1;
        }
        u64 *tmp = x;
        x = y;
        y = tmp;
        if (!changed) break;
    }
    cur = x;
    int un = 0;
    for (int v = 0; v < NN; v++) un += bits - pc(x[v]);
    return un;
}

static int dupcount(void) {
    int c = 0;
    for (int l1 = 0; l1 < dd; l1++)
        for (int l2 = l1 + 1; l2 < dd; l2++)
            for (int i = 0; i < kk; i++)
                if (layers[l1][i] == layers[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static void random_state(void) {
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < kk; i++) layers[l][i] = i;
        for (int i = kk - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = t;
        }
        for (int i = 0; i < kk; i++) {
            S[l][i] = rint_(GG);
            set_dart(l, i, layers[l][i], S[l][i]);
        }
    }
}

static int accept_move(int c2, int cost, double temp) {
    if (c2 <= cost) return 1;
    return rdbl() < exp(-(double)(c2 - cost) / temp);
}

static int anneal(int iters, int patience, clock_t deadline) {
    random_state();
    int cost = reach_count(DD) + PEN * dupcount();
    memcpy(accr, cur, sizeof(u64) * (size_t)NN);
    double c0 = cost > 1 ? (double)cost : 1.0;
    int best_cost = cost, last = 0;
    for (int t = 0; t < iters && cost != 0; t++) {
        if (t - last > patience) break;
        if (clock() > deadline) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (kk >= 2 && rdbl() < 0.25) {
            int l = rint_(dd);
            int i1 = rint_(kk);
            int i2 = rint_(kk - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1];
            layers[l][i1] = layers[l][i2];
            layers[l][i2] = tmp;
            set_dart(l, i1, layers[l][i1], S[l][i1]);
            set_dart(l, i2, layers[l][i2], S[l][i2]);
            int c2 = reach_count(DD) + PEN * dupcount();
            if (accept_move(c2, cost, temp)) {
                cost = c2;
                memcpy(accr, cur, sizeof(u64) * (size_t)NN);
                if (cost < best_cost) { best_cost = cost; last = t; }
            } else {
                tmp = layers[l][i1];
                layers[l][i1] = layers[l][i2];
                layers[l][i2] = tmp;
                set_dart(l, i1, layers[l][i1], S[l][i1]);
                set_dart(l, i2, layers[l][i2], S[l][i2]);
            }
            continue;
        }

        int l = rint_(dd), i = rint_(kk);
        if (rdbl() < 0.4) {
            int v = -1;
            for (int tr = 0; tr < 24; tr++) {
                int cand = rint_(NN);
                if (accr[cand] != FULL) { v = cand; break; }
            }
            if (v >= 0) {
                int block = v / GG;
                l = rint_(dd);
                if (block < kk) {
                    i = block;
                } else {
                    int q;
                    for (q = 0; q < kk && layers[l][q] != block - kk; q++) {}
                    i = (q < kk) ? q : rint_(kk);
                }
            }
        }
        int old = S[l][i];
        int nw = rint_(GG);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i, layers[l][i], nw);
        int c2 = reach_count(DD) + PEN * dupcount();
        if (accept_move(c2, cost, temp)) {
            cost = c2;
            memcpy(accr, cur, sizeof(u64) * (size_t)NN);
            if (cost < best_cost) { best_cost = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i, layers[l][i], old);
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double tl = atof(argv[4]);
    int best_n = atoi(argv[5]);
    int kmax = atoi(argv[6]);
    if (d < 1 || d > MAXD || D < 2 || kmax < 1) {
        printf("0 0\n");
        return 0;
    }
    if (kmax > 8) kmax = 8;
    dd = d;
    DD = D;
    rs ^= (u64)seed * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    clock_t deadline = clock() + (clock_t)(tl * (double)CLOCKS_PER_SEC);
    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 32, 36, 40};
    int nk2 = (int)(sizeof(K2S) / sizeof(K2S[0]));

    int found = 0, bK = 0, bM = 0, bK2 = 1, bR = 1;
    static int bl[MAXD][MAXK], bS[MAXD][MAXK];

    while (clock() < deadline) {
        int k = 1 + rint_(kmax);
        int Gmin = best_n / (2 * k) + 1;
        int Gt = Gmin + rint_(Gmin / 8 + 2);
        int kc = K2S[rint_(nk2)];
        if (kc > Gt) kc = 1;
        int m = (Gt + kc - 1) / kc;
        if (m < 1) m = 1;
        int r = 1;
        if (kc > 1 && m >= 3) {
            for (int tr = 0; tr < 60; tr++) {
                int c = 2 + rint_(m - 2);
                if (gcd_(c, m) == 1 && powmod(c, kc, m) == 1 % m) { r = c; break; }
            }
        }
        setup_group(m, kc, r);
        kk = k;
        NN = 2 * kk * GG;
        if (NN <= best_n || 2 * kk > 32) {
            free_group();
            continue;
        }
        FULL = (1ULL << (2 * kk)) - 1;
        nbr = malloc(sizeof(int) * (size_t)dd * (size_t)NN);
        bufA = malloc(sizeof(u64) * (size_t)NN);
        bufB = malloc(sizeof(u64) * (size_t)NN);
        accr = malloc(sizeof(u64) * (size_t)NN);

        int ok = anneal(60000, 6000, deadline);
        if (ok) {
            found = 1;
            best_n = NN;
            bK = kk;
            bM = mm;
            bK2 = k2;
            bR = rr;
            memcpy(bl, layers, sizeof(layers));
            memcpy(bS, S, sizeof(S));
        }
        free(nbr);
        free(bufA);
        free(bufB);
        free(accr);
        nbr = NULL;
        bufA = bufB = accr = NULL;
        free_group();
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bM, bK2, bR);
    kk = bK;
    NN = 2 * kk * GG;
    int nedges = kk * GG * dd;
    printf("%d %d\n", NN, nedges);
    for (int i = 0; i < kk; i++)
        for (int g = 0; g < GG; g++)
            for (int l = 0; l < dd; l++) {
                int j = bl[l][i];
                int s = bS[l][i];
                printf("%d %d\n", i * GG + g, (kk + j) * GG + gmul(g, s));
            }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact and structured constructions (Python).
# ----------------------------------------------------------------------------

def _try(fn, *args):
    try:
        return fn(*args)
    except Exception:
        return None


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph of degree d (needs d - 2 a prime power >= 3)."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Main entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + max(1.0, time_limit - 4.0)
    c_end = start + max(1.0, 0.82 * time_limit - 1.0)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact / structured constructions.
    if D >= 3:
        pg = _try(_best_pg, d)
        if pg is not None:
            consider(pg[0], pg[1])
        if D == 3:
            ar = _try(_araujo, d)
            if ar is not None:
                consider(ar[0], ar[1])
            if lib.is_prime_power(d - 1):
                return best

    if D == 4:
        gq = _try(_best_gq, d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Large bi-Cayley lift search in C, climbing from the current best order.
    if D >= 3 and d <= 64:
        remaining = c_end - time.monotonic()
        if remaining > 2.0:
            c_secs = remaining - 0.5
            seed_arg = int(seed) % (2 ** 31)
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, seed_arg, f"{c_secs:.2f}", best_n, 8],
                    stdin_graph=None,
                    timeout=remaining + 3.0,
                )
                n, e = lib.parse_graph_text(out)
                if n > best_n:
                    consider(n, e)
            except Exception:
                pass

    # Use spare degree in the best graph to add vertices.
    if time.monotonic() < hard_end - 1.0:
        try:
            rng = random.Random(seed)
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, hard_end)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
