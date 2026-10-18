import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New construction: bi-Cayley voltage lifts over semidirect products
# Z_m x|_r Z_k2, searched by simulated annealing in C.
#
# Vertices: A-block i holds (i, x) for x in G, B-block j holds (j, y).
# Layer l is a permutation P_l of the k blocks, with voltage s_{l,i}, and joins
# (i, x) to (P_l(i), x*s_{l,i}). Each vertex has exactly one edge per layer, so
# the graph is bipartite and d-regular (before duplicate penalties).
# Left multiplication by G is an automorphism that is transitive on each block,
# so the graph has diameter <= D iff BFS from the 2k block representatives
# reaches everything within D steps. The annealer minimises the number of
# unreached (source, vertex) pairs plus a penalty for repeated darts.
# ----------------------------------------------------------------------------

LIFT_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

#define PEN 20

static int d_, D_, k_, m_, k2_, r_, G_, N_;
static int *pw, *S, *P, *Sinv, *nb, *dist, *queue_;

static int gmul(int x, int y) {
    int a1 = x / k2_, b1 = x % k2_, a2 = y / k2_, b2 = y % k2_;
    long long t = (long long)pw[b1] * a2 % m_;
    int a = (int)((a1 + t) % m_);
    int b = (b1 + b2) % k2_;
    return a * k2_ + b;
}

static int ginv(int x) {
    int a = x / k2_, b = x % k2_;
    int nbb = (k2_ - b) % k2_;
    long long t = (long long)pw[nbb] * a % m_;
    int na = (int)((m_ - t) % m_);
    return na * k2_ + nbb;
}

static void build_nb(void) {
    int k = k_, d = d_, G = G_;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++)
            Sinv[l * k + i] = ginv(S[l * k + i]);
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) {
            int j = P[l * k + i], s = S[l * k + i];
            for (int x = 0; x < G; x++)
                nb[(i * G + x) * d + l] = (k + j) * G + gmul(x, s);
        }
        for (int i = 0; i < k; i++) {
            int j = P[l * k + i], si = Sinv[l * k + i];
            for (int y = 0; y < G; y++)
                nb[((k + j) * G + y) * d + l] = i * G + gmul(y, si);
        }
    }
}

static int dupcount(void) {
    int c = 0, k = k_, d = d_;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (P[l1 * k + i] == P[l2 * k + i] && S[l1 * k + i] == S[l2 * k + i]) c++;
    return c;
}

static long long eval_cost(void) {
    build_nb();
    int N = N_, d = d_, k = k_;
    long long tot = 0;
    for (int b = 0; b < 2 * k; b++) {
        int src = b * G_;
        memset(dist, -1, sizeof(int) * (size_t)N);
        int head = 0, tail = 0;
        dist[src] = 0;
        queue_[tail++] = src;
        while (head < tail) {
            int v = queue_[head++];
            if (dist[v] >= D_) continue;
            int *nv = nb + (size_t)v * d;
            for (int l = 0; l < d; l++) {
                int u = nv[l];
                if (dist[u] < 0) {
                    dist[u] = dist[v] + 1;
                    queue_[tail++] = u;
                }
            }
        }
        tot += N - tail;
    }
    return tot + (long long)PEN * dupcount();
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    rs ^= sd * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double limit = atof(argv[4]);
    k_ = atoi(argv[5]);
    m_ = atoi(argv[6]);
    k2_ = atoi(argv[7]);
    r_ = atoi(argv[8]);
    if (d_ < 1 || D_ < 1 || k_ < 1 || m_ < 2 || k2_ < 1 || k2_ > 64 || r_ < 1 ||
        (long long)m_ * k2_ > 100000) {
        printf("0 0\n");
        return 0;
    }
    G_ = m_ * k2_;
    N_ = 2 * k_ * G_;

    pw = malloc(sizeof(int) * (size_t)k2_);
    pw[0] = 1 % m_;
    for (int t = 1; t < k2_; t++) pw[t] = (int)((long long)pw[t - 1] * r_ % m_);
    if ((long long)pw[k2_ - 1] * r_ % m_ != 1 % m_) {
        printf("0 0\n");
        return 0;
    }

    nb = malloc(sizeof(int) * (size_t)N_ * d_);
    dist = malloc(sizeof(int) * (size_t)N_);
    queue_ = malloc(sizeof(int) * (size_t)N_);
    S = malloc(sizeof(int) * (size_t)k_ * d_);
    P = malloc(sizeof(int) * (size_t)k_ * d_);
    Sinv = malloc(sizeof(int) * (size_t)k_ * d_);
    if (!pw || !nb || !dist || !queue_ || !S || !P || !Sinv) {
        printf("0 0\n");
        return 0;
    }

    for (int l = 0; l < d_; l++) {
        for (int i = 0; i < k_; i++) P[l * k_ + i] = i;
        for (int i = k_ - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l * k_ + i];
            P[l * k_ + i] = P[l * k_ + j];
            P[l * k_ + j] = t;
        }
        for (int i = 0; i < k_; i++) S[l * k_ + i] = rint_(G_);
    }

    clock_t c0 = clock();
    long long cur = eval_cost();
    long long cost0 = cur;
    double T0 = 0.05 * (double)cost0 + 2.0, T1 = 0.3;

    while (cur != 0) {
        double el = (double)(clock() - c0) / CLOCKS_PER_SEC;
        if (el >= limit) break;
        double T = T0 * pow(T1 / T0, el / limit);

        int mv = (k_ >= 2 && rdbl() < 0.3);
        int idx1 = 0, idx2 = 0, oldv = 0;
        if (mv) {
            int l = rint_(d_);
            int i1 = rint_(k_);
            int i2 = rint_(k_ - 1);
            if (i2 >= i1) i2++;
            idx1 = l * k_ + i1;
            idx2 = l * k_ + i2;
            int t = P[idx1]; P[idx1] = P[idx2]; P[idx2] = t;
        } else {
            idx1 = rint_(d_ * k_);
            oldv = S[idx1];
            S[idx1] = rint_(G_);
        }

        long long nc = eval_cost();
        long long delta = nc - cur;
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
            cur = nc;
        } else {
            if (mv) {
                int t = P[idx1]; P[idx1] = P[idx2]; P[idx2] = t;
            } else {
                S[idx1] = oldv;
            }
        }
    }

    if (cur != 0) {
        printf("0 0\n");
        return 0;
    }
    build_nb();
    int kG = k_ * G_;
    printf("%d %d\n", N_, kG * d_);
    for (int v = 0; v < kG; v++)
        for (int l = 0; l < d_; l++)
            printf("%d %d\n", v, nb[(size_t)v * d_ + l]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)


def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
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
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
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
                cand = edges + [(v, n) for v in pick]
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


def _sample_group(gmin, rng):
    """Return (m, k2, r) for Z_m x|_r Z_k2 with m*k2 >= gmin, or None."""
    k2 = rng.choice([1, 1, 2, 2, 3, 4, 6, 8])
    m = max(2, -(-gmin // k2) + rng.randrange(0, 3))
    if k2 == 1:
        return m, 1, 1
    if k2 == 2:
        return m, 2, m - 1  # r = -1 always satisfies r^2 = 1
    for _ in range(300):
        r = rng.randrange(1, m)
        if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m:
            return m, k2, r
    return None


def _lift_search(d, D, seed, deadline, start):
    """Climb through bi-Cayley lifts of growing order; returns the best valid (n, edges)."""
    rng = random.Random(seed)
    best = start
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        k = rng.choice(_KS)
        gmin = best[0] // (2 * k) + 1 + rng.randrange(0, 3)
        g = _sample_group(gmin, rng)
        if g is None:
            continue
        m, k2, r = g
        budget = min(3.0, remaining - 0.5)
        try:
            out = lib.run_c(LIFT_SOURCE,
                            [d, D, rng.randrange(1, 1 << 30), f"{budget:.2f}", k, m, k2, r],
                            timeout=budget + 10.0)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Phase 1 (new): C-side annealing over bi-Cayley voltage lifts, climbing in order.
    if d >= 3 and D >= 2 and time_limit >= 12:
        lift_end = t0 + 0.6 * time_limit
        try:
            n1, e1 = _lift_search(d, D, seed, lift_end, best)
            consider(n1, e1)
        except Exception:
            pass  # keep the valid fallback

    # Phase 2: use spare degree of the current best graph.
    remaining = t0 + time_limit - time.monotonic()
    if remaining > 3.0:
        slack_end = time.monotonic() + min(0.8 * remaining, remaining - 2.0)
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, random.Random(seed), slack_end)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
