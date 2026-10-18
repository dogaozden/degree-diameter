"""Bi-Cayley voltage lifts found by a C annealer, with a safe K_{d,d} fallback.

Replaces the parent's Python/numpy lift search and grow-by-two phase with one C engine.
The engine samples a random base size K (1..6) and semidirect group Z_m x| Z_k2, then
anneals over the layer permutations and voltages. Cost counts (vertex, block) pairs at
distance > D, plus a penalty for duplicate darts. Cost 0 is a valid d-regular bipartite
graph, because the group acts on each side by left multiplication. The goal order is
ratcheted up on success and eased down on failure.

Exact constructions (projective planes, Araujo-Pardo-Lopez, generalized quadrangles)
are kept as seeds. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib


C_SOURCE = r'''
/* Bi-Cayley voltage lifts over semidirect groups Z_m x| Z_k2 (element a*k2+b).
 * Base: K vertices per side and d layers. Layer l pairs A_i with B_{lay[l][i]} through
 * voltage vol[l][i]: A_{i,g} ~ B_{j,g*s}. Every layer is a perfect matching, so the lift
 * is d-regular and bipartite. Left multiplication is an automorphism, so distances from
 * the block representatives decide the diameter.
 * Usage: prog d D seed time_limit   (stdin ignored)
 * stdout: "n m" + edges of the best graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXK 6
#define MAXN 20000
#define PEN 1000L

static int d, D;
static double t_stop;
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
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int M, K2, G, K, N;
static long pw[64];
static int lay[MAXD][MAXK], vol[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint32_t ra[MAXN], rb[MAXN];

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long t = (a + pw[b] * c) % M;
    return (int)(t * K2 + (b + e) % K2);
}

static int ginv(int s) {
    int a = s / K2, b = s % K2;
    int nb = (K2 - b) % K2;
    long t = (M - (pw[nb] * a) % M) % M;
    return (int)(t * K2 + nb);
}

static int gcd_i(int a, int b) {
    while (b) {
        int t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long pow_mod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void set_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    G = m * k2;
    pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) pw[b] = (pw[b - 1] * r) % m;
}

static void build_layer(int l) {
    for (int i = 0; i < K; i++) {
        int j = lay[l][i], s = vol[l][i], si = ginv(s);
        for (int g = 0; g < G; g++) {
            nbr[l][i * G + g] = (K + j) * G + gmul(g, s);
            nbr[l][(K + j) * G + g] = i * G + gmul(g, si);
        }
    }
}

/* Sum over vertices of unreached block representatives. */
static long reach_cost(void) {
    uint32_t *cur = ra, *nxt = rb;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * K; b++) cur[b * G] = 1u << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint32_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            if (x != cur[v]) changed = 1;
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) cost += 2 * K - __builtin_popcount(cur[v]);
    return cost;
}

static long dup_count(void) {
    long c = 0;
    for (int l1 = 0; l1 < d; l1++)
        for (int l2 = l1 + 1; l2 < d; l2++)
            for (int i = 0; i < K; i++)
                if (lay[l1][i] == lay[l2][i] && vol[l1][i] == vol[l2][i]) c++;
    return c;
}

static long total_cost(void) { return reach_cost() + PEN * dup_count(); }

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < K; i++) lay[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < K; i++) vol[l][i] = rndint(G);
        build_layer(l);
    }
}

/* Simulated annealing from a random state. Returns final cost (0 means valid). */
static long run_anneal(long maxit, double until, long patience) {
    random_state();
    long cost = total_cost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long best = cost, last = 0;
    for (long t = 0; t < maxit && cost > 0; t++) {
        if ((t & 7) == 0 && now() > until) break;
        if (t - last > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)maxit);
        if (temp < 0.5) temp = 0.5;
        int l = rndint(d);
        if (K >= 2 && rnd01() < 0.3) {
            int i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tmp;
            build_layer(l);
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                tmp = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tmp;
                build_layer(l);
            }
        } else {
            int i = rndint(K);
            int old = vol[l][i];
            int nv = rndint(G);
            if (nv == old) continue;
            vol[l][i] = nv;
            build_layer(l);
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
            } else {
                vol[l][i] = old;
                build_layer(l);
            }
        }
        if (cost < best) {
            best = cost;
            last = t;
        }
    }
    return cost;
}

static int bK, bM, bK2, bR, bN;
static int blay[MAXD][MAXK], bvol[MAXD][MAXK];
static int have_best = 0;

static void print_best(void) {
    set_group(bM, bK2, bR);
    K = bK;
    N = 2 * K * G;
    memcpy(lay, blay, sizeof lay);
    memcpy(vol, bvol, sizeof vol);
    for (int l = 0; l < d; l++) build_layer(l);
    printf("%d %d\n", N, d * K * G);
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++)
            for (int g = 0; g < G; g++)
                printf("%d %d\n", i * G + g, (K + lay[l][i]) * G + gmul(g, vol[l][i]));
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_stop = t0 + limit * 0.85 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 20; i++) rnd();

    if (d < 2 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    double mb;
    if (d == 2) {
        mb = 2.0 * D;
    } else {
        mb = 0;
        double p = 1;
        for (int i = 0; i < D; i++) {
            mb += p;
            p *= (d - 1);
        }
        mb *= 2;
    }
    if (mb > MAXN) mb = MAXN;

    static const int K2S[] = {1, 1, 2, 2, 3, 4, 5, 6, 8};
    double goal = 2.0 * d + 2.0;
    int bestN = 0;

    while (now() < t_stop) {
        if (bestN >= (int)mb) break;
        double left = t_stop - now();
        double cap = left / 4.0;
        if (cap < 2.0) cap = left < 2.0 ? left : 2.0;

        K = 1 + rndint(MAXK);
        int k2 = K2S[rndint(9)];
        int m = (int)(goal / (2.0 * K * k2)) + rndint(3);
        if (m < 2) m = 2;
        double nn = 2.0 * K * m * k2;
        if (nn > mb + 0.5 || nn > MAXN) continue;

        int r = 1;
        if (k2 > 1) {
            int found = 0;
            if (m > 2) {
                for (int tries = 0; tries < 100 && !found; tries++) {
                    int c = 2 + rndint(m - 2);
                    if (gcd_i(c, m) == 1 && pow_mod(c, k2, m) == 1 % m) {
                        r = c;
                        found = 1;
                    }
                }
            }
            if (!found && k2 == 2 && m > 2) {
                r = m - 1;
                found = 1;
            }
        }

        set_group(m, k2, r);
        N = 2 * K * G;
        long cost = run_anneal(400000L, now() + cap, 3000);

        if (cost == 0) {
            if (N > bestN) {
                bestN = N;
                bK = K;
                bM = m;
                bK2 = k2;
                bR = r;
                memcpy(blay, lay, sizeof lay);
                memcpy(bvol, vol, sizeof vol);
                have_best = 1;
            }
            goal = bestN * 1.02 + 1.0;
        } else {
            goal = goal * 0.995;
            double floor_goal = bestN * 1.01 + 1.0;
            if (goal < floor_goal) goal = floor_goal;
        }
        if (goal < 2.0 * d + 2.0) goal = 2.0 * d + 2.0;
        if (goal > mb) goal = mb;
    }

    if (have_best) print_best();
    else printf("0 0\n");
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Exact seeds.
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
# Saturation: add every legal missing edge between deficient opposite-side vertices.
# Distances only shrink, so validity is kept. Callers still check with lib.is_valid.
# ----------------------------------------------------------------------------

def _saturate(n, edges, d, D):
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            x = stack.pop()
            for y in adj[x]:
                if color[y] == -1:
                    color[y] = 1 - color[x]
                    stack.append(y)
    A = [v for v in range(n) if color[v] == 0 and len(adj[v]) < d]
    B = [v for v in range(n) if color[v] == 1 and len(adj[v]) < d]
    out = {(min(u, v), max(u, v)) for u, v in edges}
    for a in A:
        for b in B:
            if len(adj[a]) >= d:
                break
            if len(adj[b]) >= d or b in adj[a]:
                continue
            adj[a].add(b)
            adj[b].add(a)
            out.add((min(a, b), max(a, b)))
    return n, sorted(out)


def _safe_saturate(n, edges, d, D):
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2 and is valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

    # Exact constructions. Calibration cases return here immediately.
    if D >= 3:
        try:
            pg = _best_pg(d)
            if pg is not None:
                consider(pg[0], pg[1])
                if D == 3 and lib.is_prime_power(d - 1):
                    return best
        except Exception:
            pass
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            consider_saturated(*lib.araujo_lopez_graph(d - 2))
        except Exception:
            pass
    if D == 4:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main search: C bi-Cayley lift annealer over random semidirect groups.
    elapsed = time.monotonic() - t_start
    budget = min(0.88 * time_limit - 2.0, time_limit - elapsed - 6.0)
    if budget >= 1.0:
        try:
            text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                             timeout=budget + 8.0)
            n, e = lib.parse_graph_text(text)
            if n > 0:
                consider_saturated(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
