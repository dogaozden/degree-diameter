"""Bi-Cayley lift search with an exact C annealer, then exact small constructions as fallbacks.

Changed approach: the search is now a C simulated annealer over bi-Cayley voltage lifts on
semidirect products Z_m x| Z_k2. Left multiplication by the group is an automorphism of every
lift, so the cost is computed exactly by BFS from one representative per block. The cost is
the number of vertices unreached within distance D, plus a penalty for duplicate darts.
Python drives sizes and groups and keeps the largest graph that passes lib.is_valid.
K_{d,d} and the exact constructions remain as fallbacks.
"""
import itertools
import math
import random
import time

import lib


C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

/* Bi-Cayley lift annealer.
 * Usage: prog d D seed time_limit k m k2 r
 * Group: Z_m x| Z_k2, element (a,b) coded a*k2+b, (a,b)(c,e) = (a + r^b c, b+e).
 * Vertices: A-block i element g -> i*G+g ; B-block j element h -> (k+j)*G+h.
 * Layer l (0..d-1): A-block i joined to B-block pi[l][i] with voltage S[l][i]:
 *   (i,g) ~ (pi[l][i], g*S[l][i]).
 * Each layer is a permutation, so every vertex has degree exactly d (multi-edges penalised).
 * Left multiplication is an automorphism, so checking BFS balls of the 2k block
 * representatives is an exact diameter test.
 * Output: "N M" and the edges of a valid graph, or "0 0".
 */

#define MAXD 32
#define MAXK 16
#define MAXN 60000
#define PEN 40L

static int d, D, k, m, k2, G, N;
static long long rpow[64];
static int pi_[MAXD][MAXK];
static int S[MAXD][MAXK];
static int adj[MAXN][MAXD];
static int dist_[MAXN];
static int stamp_[MAXN];
static int queue_[MAXN];
static int cur_stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul(int x, int y) {
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    long long t = ((long long)a + rpow[b] * (long long)c) % m;
    return (int)(t * k2 + (b + e) % k2);
}

static void build_adj(void) {
    for (int l = 0; l < d; l++)
        for (int i = 0; i < k; i++) {
            int j = pi_[l][i], s = S[l][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (k + j) * G + gmul(g, s);
                adj[a][l] = b;
                adj[b][l] = a;
            }
        }
}

static long count_dups(void) {
    long dup = 0;
    for (int i = 0; i < k; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pi_[l1][i] == pi_[l2][i] && S[l1][i] == S[l2][i]) dup++;
    return dup;
}

static long bfs_unreached(int src) {
    cur_stamp++;
    int head = 0, tail = 0;
    queue_[tail++] = src;
    stamp_[src] = cur_stamp;
    dist_[src] = 0;
    while (head < tail) {
        int v = queue_[head++];
        if (dist_[v] >= D) continue;
        for (int l = 0; l < d; l++) {
            int u = adj[v][l];
            if (stamp_[u] != cur_stamp) {
                stamp_[u] = cur_stamp;
                dist_[u] = dist_[v] + 1;
                queue_[tail++] = u;
            }
        }
    }
    return (long)(N - tail);
}

static long eval_cost(void) {
    build_adj();
    long c = PEN * count_dups();
    for (int a = 0; a < 2 * k; a++) c += bfs_unreached(a * G);
    return c;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: %s d D seed time_limit k m k2 r\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double lim = atof(argv[4]);
    k = atoi(argv[5]);
    m = atoi(argv[6]);
    k2 = atoi(argv[7]);
    long long r = atoll(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 2 || k2 < 1 || k2 > 64) {
        printf("0 0\n");
        return 0;
    }
    G = m * k2;
    if ((long)2 * k * G > MAXN || G < d) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * k * G;

    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    rpow[0] = 1 % m;
    for (int t = 1; t < k2; t++) rpow[t] = (rpow[t - 1] * (r % m)) % m;

    for (int l = 0; l < d; l++) {
        for (int i = 0; i < k; i++) pi_[l][i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = pi_[l][i];
            pi_[l][i] = pi_[l][j];
            pi_[l][j] = tmp;
        }
        for (int i = 0; i < k; i++) S[l][i] = rndint(G);
    }

    double t0 = now();
    double tend = t0 + lim * 0.9 - 0.2;
    if (tend <= t0) tend = t0 + 0.05;

    long cost = eval_cost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    double T0 = 1.0 + 0.05 * c0;

    while (cost > 0) {
        double t = now();
        if (t > tend) break;
        double frac = (t - t0) / (tend - t0);
        double T = T0 * (1.0 - frac) + 0.2;

        if (k >= 2 && rnd01() < 0.2) {
            int l = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tmp = pi_[l][i1];
            pi_[l][i1] = pi_[l][i2];
            pi_[l][i2] = tmp;
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                tmp = pi_[l][i1];
                pi_[l][i1] = pi_[l][i2];
                pi_[l][i2] = tmp;
            }
        } else {
            int l = rndint(d), i = rndint(k);
            int old = S[l][i];
            int nw = rndint(G);
            if (nw == old) continue;
            S[l][i] = nw;
            long nc = eval_cost();
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) {
                cost = nc;
            } else {
                S[l][i] = old;
            }
        }
    }

    if (cost != 0) {
        printf("0 0\n");
        return 0;
    }
    build_adj();
    long edges = (long)k * G * d;
    printf("%d %ld\n", N, edges);
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            for (int l = 0; l < d; l++) printf("%d %d\n", a, adj[a][l]);
        }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact constructions.
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


# ----------------------------------------------------------------------------
# Group sampling for the bi-Cayley lifts.
# ----------------------------------------------------------------------------

_K2 = [1, 1, 2, 2, 3, 4, 5, 6, 8, 10, 12, 16, 20, 24]
_KS = (1, 2, 3)


def _sample_group(target, rng):
    """Return (m, k2, r) for Z_m x| Z_k2 with m*k2 about target, or None."""
    for _ in range(60):
        k2 = rng.choice(_K2)
        m = max(2, -(-target // k2))
        if k2 == 1:
            return m, 1, 1
        cands = [r for r in range(1, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands:
            return m, k2, rng.choice(cands)
    return None


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total
    rng = random.Random(seed)

    # Exact constructions.
    try:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
    except Exception:
        pass
    if D == 3 and lib.is_prime_power(d - 1):
        if lib.is_valid(best[0], best[1], d, D):
            return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Bi-Cayley lift search in C. The order goal starts near a fraction of the Moore bound,
    # rises after successes and eases after failures.
    moore = lib.moore_bound(d, D)
    goal = max(best_n * 1.05, 0.2 * moore)
    trials = {k: 0 for k in _KS}
    wins = {k: 0 for k in _KS}

    def pick_k():
        if rng.random() < 0.25:
            return rng.choice(_KS)
        return max(_KS, key=lambda k: (wins[k] + 1) / (trials[k] + 2) + 0.05 * rng.random())

    fails = 0
    attempt = 0
    while True:
        remaining = final - time.monotonic()
        if remaining < 2.0 or fails >= 4:
            break
        slice_ = min(remaining - 0.8, max(4.0, remaining / 3.0))
        k = pick_k()
        target = max(2, math.ceil(goal / (2 * k)) + rng.randrange(0, 3))
        g = _sample_group(target, rng)
        if g is None:
            goal = max(best_n * 1.01, goal * 0.99)
            continue
        m, k2, r = g
        G = m * k2
        n_try = 2 * k * G
        if n_try > 60000:
            goal = max(best_n * 1.01, goal * 0.99)
            continue
        if n_try <= best_n:
            goal = max(goal, best_n * 1.02)
            continue

        trials[k] += 1
        attempt += 1
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed * 7919 + attempt, round(slice_, 2),
                                        k, m, k2, r],
                             timeout=slice_ + 10)
            n, e = lib.parse_graph_text(text)
        except Exception:
            fails += 1
            continue
        fails = 0
        if n > 0 and n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n
            wins[k] += 1
            goal = max(goal, n * 1.03)
        else:
            goal = max(best_n * 1.01, goal * 0.99)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
