"""Bi-Cayley cyclic lift search with a bitset reach engine in C.

Main idea: for each block count k (1..6) and cyclic order m, look for a Z_m-lift of a
d-regular bipartite base multigraph on k+k blocks (2*k*m vertices). A C simulated-annealing
engine moves layer permutations and voltages, and uses bitset ball propagation over the
2k block representatives. Translation symmetry makes that check exact. Duplicate darts are
allowed during search and removed on output, so degree stays <= d. Each success is checked
with lib.is_valid, then saturated. Fallbacks: K_{d,d}, projective-plane and small known
constructions for D = 3 and 4.
"""
import itertools
import random
import time

import lib


C_LIFT = r'''
/* Cyclic bi-Cayley lift search.
 * Usage: prog d D k m seed time_limit
 * Base: k A-blocks and k B-blocks. Layer l is a permutation P[l] (A block i -> B block P[l][i])
 * with voltage S[l][i] in Z_m. Vertex A_{i,x} = i*m+x, B_{j,y} = (k+j)*m+y, with edges
 * A_{i,x} ~ B_{P[l][i], x+S[l][i]}. Output is the simple graph (deduplicated) or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXM 8192
#define MAXN (2 * MAXK * MAXM)

static int d, D, k, m, n;
static int P[MAXD][MAXK], Pinv[MAXD][MAXK], S[MAXD][MAXK];
static int nbr[MAXN][MAXD];
static uint32_t bufA[MAXN], bufB[MAXN];
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

static int rndint(int x) { return (int)(rnd() % (uint64_t)x); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static void rebuild_inv(int l) {
    for (int i = 0; i < k; i++) Pinv[l][P[l][i]] = i;
}

static void build_nbr(void) {
    for (int i = 0; i < k; i++)
        for (int x = 0; x < m; x++) {
            int v = i * m + x;
            for (int l = 0; l < d; l++) {
                int y = x + S[l][i];
                if (y >= m) y -= m;
                nbr[v][l] = (k + P[l][i]) * m + y;
            }
        }
    for (int j = 0; j < k; j++)
        for (int y = 0; y < m; y++) {
            int v = (k + j) * m + y;
            for (int l = 0; l < d; l++) {
                int i = Pinv[l][j];
                int x = y - S[l][i];
                if (x < 0) x += m;
                nbr[v][l] = i * m + x;
            }
        }
}

/* Number of (vertex, block) pairs where the block representative is farther than D. */
static long eval_cost(void) {
    int N = 2 * k * m;
    build_nbr();
    uint32_t *cur = bufA, *nxt = bufB;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[b * m] = 1u << b;
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < N; v++) {
            uint32_t s = cur[v];
            for (int l = 0; l < d; l++) s |= cur[nbr[v][l]];
            nxt[v] = s;
        }
        uint32_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    long cost = 0;
    int full = 2 * k;
    for (int v = 0; v < N; v++) cost += full - __builtin_popcount(cur[v]);
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    k = atoi(argv[3]);
    m = atoi(argv[4]);
    long seed = atol(argv[5]);
    double limit = atof(argv[6]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || m < 2 || m > MAXM) {
        printf("0 0\n");
        return 0;
    }
    n = 2 * k * m;
    double t_end = now() + (limit * 0.9 - 0.2);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int found = 0;
    while (!found && now() < t_end) {
        for (int l = 0; l < d; l++) {
            for (int i = 0; i < k; i++) P[l][i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = P[l][i];
                P[l][i] = P[l][j];
                P[l][j] = t;
            }
            rebuild_inv(l);
            for (int i = 0; i < k; i++) S[l][i] = rndint(m);
        }
        long cost = eval_cost();
        double T0 = 1.0 + 0.02 * (double)cost;
        const long cyc = 20000;
        for (long it = 0; it < cyc && cost > 0 && now() < t_end; it++) {
            double T = T0 * (1.0 - (double)it / (double)cyc) + 0.05;
            if (k >= 2 && rndint(4) == 0) {
                int l = rndint(d), i1 = rndint(k), i2 = rndint(k - 1);
                if (i2 >= i1) i2++;
                int t = P[l][i1];
                P[l][i1] = P[l][i2];
                P[l][i2] = t;
                rebuild_inv(l);
                long nc = eval_cost();
                if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
                    cost = nc;
                } else {
                    t = P[l][i1];
                    P[l][i1] = P[l][i2];
                    P[l][i2] = t;
                    rebuild_inv(l);
                }
            } else {
                int l = rndint(d), i = rndint(k);
                int old = S[l][i], nw = rndint(m);
                if (nw == old) continue;
                S[l][i] = nw;
                long nc = eval_cost();
                if (nc <= cost || rnd01() < exp((double)(cost - nc) / T)) {
                    cost = nc;
                } else {
                    S[l][i] = old;
                }
            }
        }
        if (cost == 0) found = 1;
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }

    static int keep[MAXD][MAXK];
    long cnt = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++) {
            int ok = 1;
            for (int l2 = 0; l2 < l; l2++)
                if (P[l2][i] == P[l][i] && S[l2][i] == S[l][i]) {
                    ok = 0;
                    break;
                }
            keep[l][i] = ok;
            if (ok) cnt += m;
        }
    printf("%d %ld\n", n, cnt);
    for (int i = 0; i < k; i++)
        for (int x = 0; x < m; x++)
            for (int l = 0; l < d; l++)
                if (keep[l][i]) {
                    int y = x + S[l][i];
                    if (y >= m) y -= m;
                    printf("%d %d\n", i * m + x, (k + P[l][i]) * m + y);
                }
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Small exact or known constructions (used as starting points and fallbacks).
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


def _saturate(n, edges, d, D):
    """Greedily add missing bipartite edges between deficient vertices; returns (n, edges).
    Adding an edge between opposite sides never breaks diameter, only shrinks distances."""
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
    """Saturate, falling back to the input if anything goes wrong or the result is invalid."""
    try:
        sn, se = _saturate(n, edges, d, D)
        if lib.is_valid(sn, se, d, D):
            return sn, se
    except Exception:
        pass
    return n, edges


# ----------------------------------------------------------------------------
# Cyclic lift search driver.
# ----------------------------------------------------------------------------

_KS = (1, 2, 3, 4, 5, 6)


def _lift_call(d, D, k, m, seed, budget):
    """Run the C lift search for Z_m lifts with k blocks per side; return a validated (n, edges) or None."""
    try:
        text = lib.run_c(C_LIFT, [d, D, k, m, seed, round(budget, 2)],
                         timeout=budget + 3.0)
        n, e = lib.parse_graph_text(text)
    except Exception:
        return None
    if n != 2 * k * m or not e:
        return None
    if not lib.is_valid(n, e, d, D):
        return None
    return n, e


def _next_m(s, k, best_n):
    """Next cyclic order to try for block count k, from the feasible/infeasible bracket."""
    m0 = max(2, best_n // (2 * k) + 1)
    lo, hi = s['lo'], s['hi']
    if lo is None and hi is None:
        return m0
    if lo is None:
        if hi <= m0:
            return None
        return max(m0, hi - max(1, hi // 100))
    if hi is None:
        return lo + max(1, lo // 60)
    if hi - lo <= 1:
        return None
    return (lo + hi) // 2


def _lift_phase(d, D, start_n, seed, deadline):
    """Search cyclic lifts with bracketed order targets; return the largest valid (n, edges) found, or None."""
    rng = random.Random(seed)
    best = None
    best_n = start_n
    st = {k: {'lo': None, 'hi': None, 'fails': {}} for k in _KS}
    wins = {k: 0 for k in _KS}
    tries = {k: 0 for k in _KS}
    call = 0
    while True:
        remaining = deadline - time.monotonic()
        if remaining < 1.5:
            break
        cands = []
        for k in _KS:
            m = _next_m(st[k], k, best_n)
            if m is not None:
                cands.append((k, m))
        if not cands:
            break
        k, m = max(cands, key=lambda km: (wins[km[0]] + 1) / (tries[km[0]] + 2)
                   + 0.05 * rng.random())
        budget = min(remaining - 0.5, max(2.0, min(8.0, remaining / 4)))
        tries[k] += 1
        call += 1
        res = _lift_call(d, D, k, m, seed * 7919 + call, budget)
        s = st[k]
        if res is not None and res[0] > best_n:
            wins[k] += 1
            best, best_n = res, res[0]
            s['lo'] = m
            if s['hi'] is not None and s['hi'] <= m:
                s['hi'] = None
        else:
            c = s['fails'].get(m, 0) + 1
            s['fails'][m] = c
            if c >= 2:
                s['hi'] = m if s['hi'] is None else min(s['hi'], m)
    return best


# ----------------------------------------------------------------------------
# build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    total = max(1.0, 0.85 * time_limit - 1.5)
    final = t0 + total

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

    def consider_saturated(n, e):
        sn, se = _safe_saturate(n, e, d, D)
        consider(sn, se)
        consider(n, e)

    # Exact constructions (calibration-style cases return immediately).
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
    if D == 4 and time.monotonic() < final:
        try:
            for q in range(min(d - 1, 9), 1, -1):
                if lib.is_prime_power(q):
                    consider(*_gq_w(q))
                    break
        except Exception:
            pass

    # Main phase: cyclic bi-Cayley lift search in C.
    try:
        found = _lift_phase(d, D, best_n, seed, final - 1.0)
        if found is not None:
            consider_saturated(*found)
    except Exception:
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
