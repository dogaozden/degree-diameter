"""Bi-Cayley (Haar-type) search over many finite groups, replacing the earlier voltage-lift search.

Vertices are A_g and B_g for g in a group G of order N. A_g is adjacent to B_{g s} for each s in a
connection set S of d distinct group elements. The graph is bipartite and d-regular. Left
multiplication is an automorphism, so the diameter is at most D iff BFS of depth D from A_e and
from B_e reaches every vertex. The C engine runs simulated annealing over S, with the group given
as a multiplication table. Groups come from permutation groups (PSL(2,7), PGL(2,7), S4 x Z_m,
A5 x Z_m, S5 x Z_2, PSL(2,7) x Z_2) and random semidirect products Z_m x| Z_k. Python builds
valid fallbacks (K_{d,d}, projective planes, Araujo-Pardo-Lopez, W(q)) and keeps the best graph.
Every returned graph is checked with lib.is_valid.
"""
import itertools
import math
import random
import time

import numpy as np

import lib

C_SOURCE = r'''
/* Bi-Cayley search over supplied finite groups.
 *
 * Usage:  prog d D seed time_limit   < input
 * Input:  "G m" then 2m ints (flat stream). The flat stream is G, then per group: N, E (identity
 *         index), then the N*N multiplication table row-major (entries 0..N-1).
 * Output: "n m" plus edges of the best bi-Cayley graph found, or "0 0".
 *
 * Vertex A_g = g, vertex B_g = N + g. Edge A_g -- B_{g*s} for each s in S (|S| = d, distinct).
 * cost(S) = unreached vertices from A_e plus unreached from B_e, within depth D. Zero means valid.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 400
#define MAXD 64
#define MAXG 64

static int d, D;
static double t_end;
static int G;
static int gN[MAXG], gE[MAXG];
static int *gmul[MAXG];
static int *ginv[MAXG];

static const int *F;
static long FC, FP;
static int FOK;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rng_state = 88172645463325252ULL;
static uint64_t rnd(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

static int nextv(void) {
    if (FP >= FC) { FOK = 0; return 0; }
    return F[FP++];
}

static int vis[2 * MAXN];
static int vstamp = 0;
static int qb[2 * MAXN];
static int qdist[2 * MAXN];

/* Number of vertices reached from src within distance D. */
static int bfs_reach(int g, const int *S, const int *Si, int src) {
    int N = gN[g];
    const int *M = gmul[g];
    vstamp++;
    int qh = 0, qt = 0;
    qb[qt] = src;
    qdist[qt] = 0;
    qt++;
    vis[src] = vstamp;
    while (qh < qt) {
        int v = qb[qh], dv = qdist[qh];
        qh++;
        if (dv >= D) continue;
        if (v < N) {
            const int *row = M + (size_t)v * N;
            for (int i = 0; i < d; i++) {
                int u = N + row[S[i]];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    qb[qt] = u;
                    qdist[qt] = dv + 1;
                    qt++;
                }
            }
        } else {
            const int *row = M + (size_t)(v - N) * N;
            for (int i = 0; i < d; i++) {
                int u = row[Si[i]];
                if (vis[u] != vstamp) {
                    vis[u] = vstamp;
                    qb[qt] = u;
                    qdist[qt] = dv + 1;
                    qt++;
                }
            }
        }
    }
    return qt;
}

static long eval_cost(int g, const int *S, int *Si) {
    int N = gN[g];
    const int *iv = ginv[g];
    for (int i = 0; i < d; i++) Si[i] = iv[S[i]];
    long n2 = 2L * N;
    return (n2 - bfs_reach(g, S, Si, 0)) + (n2 - bfs_reach(g, S, Si, N));
}

static int in_set(const int *S, int k, int x) {
    for (int i = 0; i < k; i++)
        if (S[i] == x) return 1;
    return 0;
}

/* Simulated annealing over connection sets of group g. Returns 1 with a valid S, or 0 at timeout. */
static int anneal(int g, double until, int *S) {
    int N = gN[g];
    int Si[MAXD];
    if (N < d) return 0;
    for (;;) {
        for (int i = 0; i < d; i++) {
            int x;
            do { x = rndint(N); } while (in_set(S, i, x));
            S[i] = x;
        }
        long cost = eval_cost(g, S, Si);
        for (long it = 0; it < 40000; it++) {
            if (cost == 0) return 1;
            if ((it & 255) == 0 && now() > until) return 0;
            double T = 2.0 * pow(0.05, (double)it / 40000.0) + 0.05;
            int i = rndint(d), x = rndint(N);
            if (in_set(S, d, x)) continue;
            int old = S[i];
            S[i] = x;
            long c2 = eval_cost(g, S, Si);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else S[i] = old;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < input\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.95;
    rng_state ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rng_state) rng_state = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int hdr_n, hdr_m;
    if (scanf("%d %d", &hdr_n, &hdr_m) != 2 || hdr_m < 0 || hdr_m > 50000000) {
        printf("0 0\n");
        return 0;
    }
    long cnt = 2L * hdr_m;
    int *flat = malloc(sizeof(int) * (size_t)(cnt + 2));
    if (!flat) { printf("0 0\n"); return 0; }
    for (long i = 0; i < cnt; i++) {
        if (scanf("%d", &flat[i]) != 1) { printf("0 0\n"); return 0; }
    }
    F = flat;
    FC = cnt;
    FP = 0;
    FOK = 1;

    int ng = nextv();
    if (!FOK || ng <= 0 || ng > MAXG) { printf("0 0\n"); return 0; }
    G = 0;
    for (int g = 0; g < ng; g++) {
        int N = nextv(), E = nextv();
        if (!FOK || N < 1 || N > MAXN || E < 0 || E >= N) break;
        gN[G] = N;
        gE[G] = E;
        gmul[G] = malloc(sizeof(int) * (size_t)N * (size_t)N);
        ginv[G] = malloc(sizeof(int) * (size_t)N);
        if (!gmul[G] || !ginv[G]) break;
        int okg = 1;
        for (long q = 0; q < (long)N * N; q++) {
            int v = nextv();
            if (!FOK || v < 0 || v >= N) { okg = 0; break; }
            gmul[G][q] = v;
        }
        if (!okg) break;
        for (int x = 0; x < N && okg; x++) {
            ginv[G][x] = -1;
            for (int y = 0; y < N; y++)
                if (gmul[G][(size_t)x * N + y] == E) { ginv[G][x] = y; break; }
            if (ginv[G][x] < 0) okg = 0;
        }
        if (!okg) break;
        G++;
    }

    long moore = moore_bound();
    int bestN = 0, bestG = -1;
    int bestS[MAXD];
    int S[MAXD];
    int progress = 1;
    while (progress && now() < t_end) {
        progress = 0;
        for (int g = 0; g < G && now() < t_end; g++) {
            int N = gN[g];
            if (N <= bestN || 2L * N > moore || N < d) continue;
            progress = 1;
            double until = now() + 1.5;
            if (until > t_end) until = t_end;
            if (anneal(g, until, S)) {
                bestN = N;
                bestG = g;
                memcpy(bestS, S, sizeof(int) * (size_t)d);
                if (2L * bestN >= moore) { progress = 0; break; }
            }
        }
    }

    if (bestG < 0) {
        printf("0 0\n");
        return 0;
    }
    int N = gN[bestG];
    const int *M = gmul[bestG];
    printf("%d %d\n", 2 * N, N * d);
    for (int g = 0; g < N; g++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", g, N + M[(size_t)g * N + bestS[i]]);
    return 0;
}
'''

MAX_GROUPS = 16      # groups passed to the C engine
MAX_ORDER = 400      # largest group order handled by the C engine
SEMI_SAMPLES = 14    # random semidirect orders sampled per call


# ----------------------------------------------------------------------------
# Group constructions (multiplication tables with identity index 0 for perm groups)
# ----------------------------------------------------------------------------

def _perm_closure(gens):
    """Closure of permutation generators (tuples); returns (elements, index) or None if too big."""
    npts = len(gens[0])
    ident = tuple(range(npts))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for x in frontier:
            for g in gens:
                y = tuple(g[i] for i in x)
                if y not in index:
                    if len(elems) >= MAX_ORDER:
                        return None
                    index[y] = len(elems)
                    elems.append(y)
                    nxt.append(y)
        frontier = nxt
    return elems, index


def _perm_group_table(gens):
    """(N, identity index, mul table as numpy array) for a permutation group, or None."""
    res = _perm_closure(gens)
    if res is None:
        return None
    elems, index = res
    N = len(elems)
    mul = np.empty((N, N), dtype=np.int64)
    for a, pa in enumerate(elems):
        for b, pb in enumerate(elems):
            mul[a, b] = index[tuple(pa[i] for i in pb)]
    return N, 0, mul


def _cyc(m):
    """Generator list for the cyclic group of order m acting on m points."""
    return [tuple((i + 1) % m for i in range(m))]


def _direct(A, B):
    """Generators of the direct product of two permutation groups on disjoint point sets."""
    na, nb = len(A[0]), len(B[0])
    tot = na + nb

    def emb(p, off):
        q = list(range(tot))
        for i, x in enumerate(p):
            q[off + i] = off + x
        return tuple(q)

    return [emb(p, 0) for p in A] + [emb(p, na) for p in B]


def _perm_specs():
    """Generator lists for a family of groups with orders from 24 to about 336."""
    A5 = [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0)]
    S5 = [(1, 2, 0, 3, 4), (1, 2, 3, 4, 0), (1, 0, 2, 3, 4)]
    S4 = [(1, 0, 2, 3), (1, 2, 3, 0)]
    g1 = tuple([(i + 1) % 7 for i in range(7)] + [7])        # x -> x + 1 on the projective line
    g2 = tuple([(2 * i) % 7 for i in range(7)] + [7])        # x -> 2x
    g3 = tuple([7] + [(-pow(i, 5, 7)) % 7 for i in range(1, 7)] + [0])  # x -> -1/x
    h = tuple([(3 * i) % 7 for i in range(7)] + [7])         # x -> 3x (non-square)
    PSL = [g1, g2, g3]
    PGL = [g1, g2, g3, h]
    specs = [PSL, PGL]
    specs += [_direct(S4, _cyc(m)) for m in range(7, 15)]
    specs += [_direct(A5, _cyc(m)) for m in (3, 4, 5)]
    specs.append(_direct(S5, _cyc(2)))
    specs.append(_direct(PSL, _cyc(2)))
    return specs


def _semidirect_table(m, k, r):
    """(N, identity index, table) for Z_m x| Z_k with element (a, b) coded as a*k + b."""
    N = m * k
    idx = np.arange(N, dtype=np.int64)
    a = idx // k
    b = idx % k
    rp = np.array([pow(r, j, m) for j in range(k)], dtype=np.int64)
    A = (a[:, None] + rp[b][:, None] * a[None, :]) % m
    B = (b[:, None] + b[None, :]) % k
    return N, 0, A * k + B


def _semi_groups(lo, hi, rng):
    """Random semidirect products Z_m x| Z_k with order in [lo, hi] (cyclic when no choice works)."""
    out = []
    Ns = list(range(lo, hi + 1))
    rng.shuffle(Ns)
    for N in Ns[:SEMI_SAMPLES]:
        divs = [m for m in range(2, N + 1) if N % m == 0]
        if not divs:
            continue
        choice = (N, 1, 1)  # cyclic Z_N
        for _ in range(300):
            m = rng.choice(divs)
            k = N // m
            r = rng.randrange(1, m)
            if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                choice = (m, k, r)
                break
        out.append(_semidirect_table(*choice))
    return out


def _groups(lo, hi, seed):
    """Group tables with order in [lo, hi], largest order first, at most MAX_GROUPS."""
    rng = random.Random(seed)
    cands = []
    for gens in _perm_specs():
        t = _perm_group_table(gens)
        if t is not None and lo <= t[0] <= hi:
            cands.append(t)
    cands += _semi_groups(lo, hi, rng)
    cands.sort(key=lambda t: -t[0])
    if len(cands) > MAX_GROUPS:
        step = len(cands) / MAX_GROUPS
        cands = [cands[int(i * step)] for i in range(MAX_GROUPS)]
    return cands


def _encode(groups):
    """Pack the group tables into the (n, edges) form that lib.run_c writes to stdin."""
    flat = [len(groups)]
    for N, E, T in groups:
        flat.append(N)
        flat.append(E)
        flat.extend(T.ravel().tolist())
    if len(flat) % 2:
        flat.append(0)
    pairs = list(zip(flat[0::2], flat[1::2]))
    return 1, pairs


# ----------------------------------------------------------------------------
# Python fallback constructions (valid graphs the search can only improve on)
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo_lopez(d):
    """Araujo-Pardo and Lopez family for d = q + 2, q a prime power >= 3."""
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
    """W(q) for the largest prime power q with q + 1 <= d, capped at q = 5."""
    for q in range(min(d - 1, 5), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _candidates(d, D):
    """Valid constructions for (d, D); each builder is guarded."""
    builders = []
    if D >= 3:
        builders.append(lambda: _best_pg(d))
        builders.append(lambda: _araujo_lopez(d))
    if D >= 4:
        builders.append(lambda: _best_gq(d))
    out = []
    for b in builders:
        try:
            r = b()
        except Exception:
            r = None
        if r is not None:
            out.append(r)
    return out


# ----------------------------------------------------------------------------
# Entry point
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d}: diameter 2, and optimal for D = 2 (Moore bound 2d).
    best = lib.haar_graph(d, range(d))
    if not lib.is_valid(best[0], best[1], d, D):
        best = (1, [])
    if D == 2:
        return best

    for n, e in _candidates(d, D):
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    hi = min(moore // 2, MAX_ORDER)     # bi-Cayley order N gives 2N vertices
    lo = best[0] // 2 + 1
    if best[0] >= moore or hi < max(lo, d):
        return best

    try:
        groups = _groups(lo, hi, seed)
    except Exception:
        return best
    if not groups:
        return best
    stdin_graph = _encode(groups)

    elapsed = time.monotonic() - t0
    budget = 0.85 * time_limit - elapsed - 1.0
    timeout = 0.95 * time_limit - elapsed
    if budget < 3 or timeout < budget:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=stdin_graph, timeout=timeout)
        n, e = lib.parse_graph_text(text)
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    except Exception:
        pass  # keep the valid Python-built fallback

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
