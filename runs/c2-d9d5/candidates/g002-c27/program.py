import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over Z_m x| Z_k2.
#
# Vertices: A_{i,g} = i*G + g (i < k), B_{p,h} = (k+p)*G + h, G = m*k2.
# Layer l pairs A_i with B_{layers[l][i]} through voltage s:
#   A_{i,g} ~ B_{p, g*s},   B_{p,h} ~ A_{i, h*s^-1}.
# Left multiplication is an automorphism, so the graph has diameter <= D iff
# every vertex is within distance D of every block identity e_c. The reach
# bitmask per vertex tracks this.
#
# The search is simulated annealing with iterated-local-search kicks, run in C.
# Trials pick a base size k (bandit) and a random group of order just above
# the current best. The engine prints the largest valid graph it found with
# more vertices than the starting threshold, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PENALTY 1000LL
#define MAXD 64
#define MAXK 8
#define KICK 3
#define ITERS 40000LL
#define PATIENCE 3000LL
#define MAXRESTART 4

static int d_, D_, k_, G_, N_;
static long long m_, k2_, pw_[64];
static int *nbr;
static uint32_t *curR, *candR, *scrR;
static int layers[MAXD][MAXK];
static int S[MAXD][MAXK];
static uint64_t rs;

static uint64_t rnd64(void) {
    uint64_t z = (rs += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}
static int rnd(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static long long gcdll(long long a, long long b) {
    if (a < 0) a = -a;
    if (b < 0) b = -b;
    while (b) { long long t = a % b; a = b; b = t; }
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

/* (a,b)*(c,e) = (a + r^b c, b + e) with element coded a*k2 + b. */
static int gmul(int x, int y) {
    long long k2 = k2_, m = m_;
    long long a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = (a + pw_[b] * c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

/* inverse of (a,b) is (-r^{-b} a, -b). */
static int ginv(int x) {
    long long k2 = k2_, m = m_;
    long long a = x / k2, b = x % k2;
    long long nb = (k2 - b) % k2;
    long long t = pw_[nb] * a % m;
    long long na = (m - t) % m;
    return (int)(na * k2 + nb);
}

static void set_dart(int l, int i) {
    const int N = N_, G = G_, k = k_;
    int s = S[l][i], p = layers[l][i];
    int si = ginv(s);
    int *row = nbr + (size_t)l * N;
    for (int g = 0; g < G; g++) {
        row[i * G + g] = (k + p) * G + gmul(g, s);
        row[(k + p) * G + g] = i * G + gmul(g, si);
    }
}

static void rebuild_all(void) {
    for (int l = 0; l < d_; l++)
        for (int i = 0; i < k_; i++)
            set_dart(l, i);
}

/* out[v] bit c is set iff the identity of block c is within distance D_ of v. */
static void compute_reach(uint32_t *out) {
    const int N = N_, k = k_, d = d_;
    uint32_t *a = out, *b = scrR;
    for (int v = 0; v < N; v++) a[v] = 0;
    for (int blk = 0; blk < 2 * k; blk++) a[blk * G_] = 1u << blk;
    for (int t = 0; t < D_; t++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t r = a[v];
            for (int l = 0; l < d; l++) r |= a[nbr[(size_t)l * N + v]];
            b[v] = r;
            if (r != a[v]) changed = 1;
        }
        uint32_t *tmp = a; a = b; b = tmp;
        if (!changed) break;
    }
    if (a != out) memcpy(out, a, sizeof(uint32_t) * (size_t)N);
}

static int pc32(uint32_t x) {
    int c = 0;
    while (x) { x &= x - 1; c++; }
    return c;
}

static long long dupcount(void) {
    long long c = 0;
    for (int i = 0; i < k_; i++)
        for (int l = 0; l < d_; l++)
            for (int l2 = l + 1; l2 < d_; l2++)
                if (layers[l][i] == layers[l2][i] && S[l][i] == S[l2][i]) c++;
    return c;
}

/* Cost of the current state, with reach computed into candR. */
static long long eval_cand(void) {
    compute_reach(candR);
    long long unr = 0;
    const int N = N_, k = k_;
    for (int v = 0; v < N; v++) unr += 2 * k - pc32(candR[v]);
    return unr + PENALTY * dupcount();
}

static void accept(void) {
    uint32_t *t = curR;
    curR = candR;
    candR = t;
}

static void snapshot(int bl[MAXD][MAXK], int bs[MAXD][MAXK]) {
    memcpy(bl, layers, sizeof(layers));
    memcpy(bs, S, sizeof(S));
}

static void restore(const int bl[MAXD][MAXK], const int bs[MAXD][MAXK]) {
    memcpy(layers, bl, sizeof(layers));
    memcpy(S, bs, sizeof(S));
}

static int search(double deadline) {
    const int d = d_, k = k_, G = G_;
    const long long iters = ITERS;
    const uint32_t full = (1u << (2 * k)) - 1u;

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) layers[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rnd(i + 1);
            int tmp = layers[l][i];
            layers[l][i] = layers[l][j];
            layers[l][j] = tmp;
        }
        for (int i = 0; i < k; i++) S[l][i] = rnd(G);
    }
    rebuild_all();
    long long cost = eval_cand();
    accept();

    double c0 = cost > 1 ? (double)cost : 1.0;
    long long best_cost = cost;
    static int bestL[MAXD][MAXK], bestS[MAXD][MAXK];
    snapshot(bestL, bestS);
    long long last_improve = 0;
    int restarts = 0;

    for (long long t = 0; t < iters; t++) {
        if (cost == 0) break;
        if ((t & 63) == 0 && now_s() > deadline) break;

        if (t - last_improve > PATIENCE) {
            restarts++;
            if (restarts > MAXRESTART) break;
            restore(bestL, bestS);
            rebuild_all();
            for (int q = 0; q < KICK; q++) {
                int l = rnd(d), i = rnd(k);
                S[l][i] = rnd(G);
                set_dart(l, i);
            }
            cost = eval_cand();
            accept();
            last_improve = t;
            continue;
        }

        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rndu() < 0.25) {
            int l = rnd(d);
            int i1 = rnd(k), i2 = rnd(k - 1);
            if (i2 >= i1) i2++;
            int tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
            set_dart(l, i1);
            set_dart(l, i2);
            long long c2 = eval_cand();
            if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                accept();
                if (cost < best_cost) {
                    best_cost = cost;
                    last_improve = t;
                    snapshot(bestL, bestS);
                }
            } else {
                tmp = layers[l][i1]; layers[l][i1] = layers[l][i2]; layers[l][i2] = tmp;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        int l = -1, i = -1;
        if (rndu() < 0.4) {
            int nbad = 0, pick = -1;
            for (int v = 0; v < N_; v++) {
                if (curR[v] != full) {
                    nbad++;
                    if (rnd(nbad) == 0) pick = v;
                }
            }
            if (pick >= 0) {
                int blk = pick / G;
                l = rnd(d);
                if (blk < k) {
                    i = blk;
                } else {
                    for (int j = 0; j < k; j++)
                        if (layers[l][j] == blk - k) { i = j; break; }
                }
            }
        }
        if (i < 0) {
            l = rnd(d);
            i = rnd(k);
        }

        int old = S[l][i];
        int nw = rnd(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long long c2 = eval_cand();
        if (c2 <= cost || rndu() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            accept();
            if (cost < best_cost) {
                best_cost = cost;
                last_improve = t;
                snapshot(bestL, bestS);
            }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static void extract(int *out) {
    long long idx = 0;
    int KG = k_ * G_;
    for (int u = 0; u < KG; u++)
        for (int l = 0; l < d_; l++) {
            out[2 * idx] = u;
            out[2 * idx + 1] = nbr[(size_t)l * N_ + u];
            idx++;
        }
}

static const int K2CH[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

static int sample_group(long long target, int *mo, int *k2o, int *ro) {
    for (int tries = 0; tries < 200; tries++) {
        int k2 = K2CH[rnd(20)];
        long long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        long long r = -1;
        if (k2 == 1) {
            r = 1 % m;
        } else if (k2 == 2 && rndu() < 0.3) {
            r = m - 1;
            if (gcdll(r, m) != 1 || (r * r) % m != 1 % m) continue;
        } else {
            for (int q = 0; q < 60; q++) {
                long long c = (m > 2) ? 2 + rnd((int)(m - 2)) : 1;
                if (gcdll(c, m) == 1 && powmod(c, k2, m) == 1 % m) { r = c; break; }
            }
            if (r < 0) continue;
        }
        *mo = (int)m;
        *k2o = k2;
        *ro = (int)r;
        return 1;
    }
    return 0;
}

static int pick_k(const long long *trials, const long long *wins) {
    if (rndu() < 0.2) return 1 + rnd(4);
    int bestk = 1;
    double bv = -1.0;
    for (int k = 1; k <= 4; k++) {
        double v = (double)(wins[k] + 1) / (double)(trials[k] + 2) + 0.02 * rndu();
        if (v > bv) { bv = v; bestk = k; }
    }
    return bestk;
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    long long best_n = atoll(argv[5]);
    if (d < 3 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }

    rs = (uint64_t)seed * 0x2545F4914F6CDD1DULL + 0x1234567ULL;
    d_ = d;
    D_ = D;
    double deadline = now_s() + budget;

    long long trials[5] = {0, 0, 0, 0, 0};
    long long wins[5] = {0, 0, 0, 0, 0};
    int *bestE = NULL;
    long long bestCnt = 0, bestN = 0;

    while (now_s() < deadline) {
        int k = pick_k(trials, wins);
        long long base = best_n / (2LL * k);
        long long extra = base / 8 + 1;
        if (extra < 2) extra = 2;
        long long target = base + 1 + (long long)rnd((int)extra);
        if (target < 2) target = 2;

        int m, k2, r;
        if (!sample_group(target, &m, &k2, &r)) continue;
        long long G = (long long)m * k2;
        long long N = 2LL * k * G;
        if (N <= best_n || N > 200000) continue;

        k_ = k;
        G_ = (int)G;
        N_ = (int)N;
        m_ = m;
        k2_ = k2;
        pw_[0] = 1 % m;
        for (int t = 1; t < k2; t++) pw_[t] = pw_[t - 1] * r % m;

        trials[k]++;
        nbr = malloc(sizeof(int) * (size_t)d * (size_t)N);
        curR = malloc(sizeof(uint32_t) * (size_t)N);
        candR = malloc(sizeof(uint32_t) * (size_t)N);
        scrR = malloc(sizeof(uint32_t) * (size_t)N);
        if (!nbr || !curR || !candR || !scrR) {
            free(nbr); free(curR); free(candR); free(scrR);
            nbr = NULL; curR = candR = scrR = NULL;
            break;
        }

        int ok = search(deadline);
        if (ok) {
            wins[k]++;
            long long cnt = (long long)k * G * d;
            int *E = malloc(sizeof(int) * 2 * (size_t)cnt);
            if (E) {
                extract(E);
                free(bestE);
                bestE = E;
                bestCnt = cnt;
                bestN = N;
                best_n = N;
            }
        }

        free(nbr); free(curR); free(candR); free(scrR);
        nbr = NULL;
        curR = candR = scrR = NULL;
    }

    if (bestE) {
        printf("%lld %lld\n", bestN, bestCnt);
        for (long long i = 0; i < bestCnt; i++)
            printf("%d %d\n", bestE[2 * i], bestE[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    free(bestE);
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
# Main entry point.
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

    # Exact constructions: return immediately (calibration-style cases).
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

    # Main search in C, starting from the best order found so far.
    if d >= 3 and D >= 3 and time.monotonic() < deadline - 1.0:
        c_budget = deadline - time.monotonic()
        try:
            text = lib.run_c(C_SOURCE,
                             [d, D, seed & 0x7FFFFFFF, f"{c_budget:.2f}", best_n],
                             timeout=c_budget + 5.0)
            n2, e2 = lib.parse_graph_text(text)
            consider(n2, e2)
        except (RuntimeError, ValueError):
            pass

    # Use any spare degree in the best graph to add vertices.
    if time.monotonic() < final_deadline:
        n2, e2 = _slack_extend(best[0], best[1], d, D, rng, final_deadline)
        consider(n2, e2)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
