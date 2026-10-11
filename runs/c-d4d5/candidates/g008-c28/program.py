"""Bold variant: bi-Cayley search over non-cyclic groups.

The graph is the bi-Cayley graph of a group G of order N with connection set S of size d:
vertices (g,0) and (g,1), with (g,0) adjacent to (g*s,1) for s in S. Left multiplication by G
is an automorphism, so the diameter test needs only two BFS runs, from (e,0) and (e,1).

Groups come from semidirect products Z_m x| Z_k, direct products with small non-abelian
groups (S3, D4, A4, S4, A5, S5, GL(2,3), Z3 wr Z3), and cyclic products. The C engine
hill-climbs S over all candidate groups in round-robin slices and returns the largest order
it finds. Every result is re-checked with lib.is_valid. If the search finds nothing, the
algebraic starts or K_{d,d} are returned. This is a high-risk change: it drops the old
voltage-lift search, so a target case can fall back to a smaller valid graph.
"""
import itertools
import math
import random
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 32
#define MAXQ 2048
#define MAXGR 128
#define PATIENCE 4000L
#define SLICE 2000

typedef struct {
    int id, N;
    int *mul, *inv;
    int S[MAXD];
    int cur;
    long since;
} Grp;

static int d, D;
static Grp grp[MAXGR];
static int ngr;
static int dist_[MAXQ], que[MAXQ];
static int Sinv[MAXD];

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

/* Vertices 0..N-1 are side 0 (element x), N..2N-1 are side 1 (element y).
   Side-0 x ~ side-1 x*s for s in S. Returns unreached counts from (e,0) and (e,1). */
static int bad_of(const Grp *g, const int *S) {
    int N = g->N, tot = 2 * N;
    for (int i = 0; i < d; i++) Sinv[i] = g->inv[S[i]];
    long bad = 0;
    for (int src = 0; src < 2; src++) {
        for (int v = 0; v < tot; v++) dist_[v] = -1;
        int head = 0, tail = 0, s0 = src * N;
        dist_[s0] = 0;
        que[tail++] = s0;
        while (head < tail) {
            int v = que[head++];
            if (dist_[v] >= D) continue;
            if (v < N) {
                const int *row = g->mul + (size_t)v * N;
                for (int i = 0; i < d; i++) {
                    int u = N + row[S[i]];
                    if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; que[tail++] = u; }
                }
            } else {
                const int *row = g->mul + (size_t)(v - N) * N;
                for (int i = 0; i < d; i++) {
                    int u = row[Sinv[i]];
                    if (dist_[u] < 0) { dist_[u] = dist_[v] + 1; que[tail++] = u; }
                }
            }
        }
        bad += tot - tail;
    }
    return (int)bad;
}

static void rand_S(const Grp *g, int *S) {
    for (int i = 0; i < d; i++) {
        for (;;) {
            int x = rndint(g->N), ok = 1;
            for (int j = 0; j < i; j++)
                if (S[j] == x) { ok = 0; break; }
            if (ok) { S[i] = x; break; }
        }
    }
}

static void init_group(Grp *g) {
    g->since = 0;
    rand_S(g, g->S);
    g->cur = bad_of(g, g->S);
}

static void run_steps(Grp *g, int steps) {
    for (int s = 0; s < steps && g->cur > 0; s++) {
        if (g->since > PATIENCE) {
            rand_S(g, g->S);
            g->cur = bad_of(g, g->S);
            g->since = 0;
            continue;
        }
        int i = rndint(d), old = g->S[i], x = rndint(g->N), dup = 0;
        for (int j = 0; j < d; j++)
            if (g->S[j] == x) { dup = 1; break; }
        if (dup) { g->since++; continue; }
        g->S[i] = x;
        int nb = bad_of(g, g->S);
        if (nb <= g->cur || rnd01() < 0.02) {
            if (nb < g->cur) g->since = 0; else g->since++;
            g->cur = nb;
        } else {
            g->S[i] = old;
            g->since++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    int n0, m0, cnt = 0;
    if (scanf("%d %d", &n0, &m0) != 2 || d < 1 || d > MAXD || D < 1) { puts("NONE"); return 0; }
    if (scanf("%d", &cnt) != 1) cnt = 0;
    if (cnt > MAXGR) cnt = MAXGR;
    ngr = cnt;

    for (int gi = 0; gi < cnt; gi++) {
        Grp *g = &grp[gi];
        int N = 0;
        g->id = gi;
        g->N = 0;
        g->mul = NULL;
        g->inv = NULL;
        g->since = 0;
        if (scanf("%d", &N) != 1 || N < 0 || N > MAXQ / 2) { puts("NONE"); return 0; }
        g->mul = malloc(sizeof(int) * (size_t)(N * N + 1));
        g->inv = malloc(sizeof(int) * (size_t)(N + 1));
        for (int k = 0; k < N * N; k++)
            if (scanf("%d", &g->mul[k]) != 1) { puts("NONE"); return 0; }
        int ok = N >= d && N > 0;
        for (int x = 0; x < N && ok; x++) {
            g->inv[x] = -1;
            for (int y = 0; y < N; y++)
                if (g->mul[x * N + y] == 0) { g->inv[x] = y; break; }
            if (g->inv[x] < 0) ok = 0;
        }
        if (ok) {
            g->N = N;
            init_group(g);
        }
    }

    int bestN = 0, bestg = -1, bestS[MAXD];
    for (;;) {
        int active = 0;
        for (int gi = 0; gi < ngr && now() < t_end; gi++) {
            Grp *g = &grp[gi];
            if (g->N <= bestN) continue;
            active = 1;
            run_steps(g, SLICE);
            if (g->cur == 0) {
                bestN = g->N;
                bestg = gi;
                memcpy(bestS, g->S, sizeof(int) * d);
            }
        }
        if (!active || now() >= t_end) break;
    }

    if (bestg < 0) { puts("NONE"); return 0; }
    printf("%d\n", grp[bestg].id);
    for (int i = 0; i < d; i++) printf("%d ", bestS[i]);
    printf("\n");
    return 0;
}
'''


def _gq_w(q):
    """Incidence graph of points and lines of W(q): degree q+1, diameter 4."""
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


def _largest_prime_power_le(x):
    for q in range(x, 1, -1):
        if lib.is_prime_power(q):
            return q
    return None


def known_starts(d, D):
    """Algebraic candidates valid for diameter D (may be empty)."""
    out = []
    if D >= 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
        out.append(lib.projective_plane_incidence(d - 1))
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        out.append(lib.araujo_lopez_graph(d - 2))
    if D >= 4:
        q = _largest_prime_power_le(min(d - 1, 9))
        if q is not None and q >= 2:
            out.append(_gq_w(q))
    return out


# ---------------------------------------------------------------- group tables
# A group is (N, flat) with flat[x*N + y] = x*y, identity 0.

def _perm(n, cycles):
    p = list(range(n))
    for c in cycles:
        for i, x in enumerate(c):
            p[x] = c[(i + 1) % len(c)]
    return tuple(p)


def _matrix_perm(M):
    pts = [(a, b) for a in range(3) for b in range(3) if (a, b) != (0, 0)]
    idx = {v: i for i, v in enumerate(pts)}
    return tuple(idx[((M[0][0] * v[0] + M[0][1] * v[1]) % 3,
                      (M[1][0] * v[0] + M[1][1] * v[1]) % 3)] for v in pts)


def _closure(gens, limit):
    """Permutation group generated by gens as (N, flat), identity first; None if order > limit."""
    n = len(gens[0])
    ident = tuple(range(n))
    elems = [ident]
    index = {ident: 0}
    frontier = [ident]
    while frontier:
        nxt = []
        for p in frontier:
            for g in gens:
                q = tuple(g[x] for x in p)
                if q not in index:
                    index[q] = len(elems)
                    elems.append(q)
                    nxt.append(q)
                    if len(elems) > limit:
                        return None
        frontier = nxt
    N = len(elems)
    flat = [0] * (N * N)
    for i, a in enumerate(elems):
        for j, b in enumerate(elems):
            flat[i * N + j] = index[tuple(a[x] for x in b)]
    return N, flat


def _semidirect_table(m, k, r):
    N, mul, _ = lib.semidirect_group(m, k, r)
    return N, [mul(x, y) for x in range(N) for y in range(N)]


def _direct(X, Y):
    N1, m1 = X
    N2, m2 = Y
    N = N1 * N2
    flat = [0] * (N * N)
    for x in range(N):
        a, b = divmod(x, N2)
        for y in range(N):
            c, e = divmod(y, N2)
            flat[x * N + y] = m1[a * N1 + c] * N2 + m2[b * N2 + e]
    return N, flat


def _gens_list():
    return [
        [_perm(3, [[0, 1]]), _perm(3, [[0, 1, 2]])],                       # S3
        [_perm(4, [[0, 1, 2, 3]]), _perm(4, [[1, 3]])],                    # D4
        [_perm(4, [[0, 1, 2]]), _perm(4, [[0, 1], [2, 3]])],               # A4
        [_perm(4, [[0, 1]]), _perm(4, [[0, 1, 2, 3]])],                    # S4
        [_perm(5, [[0, 1, 2]]), _perm(5, [[2, 3, 4]])],                    # A5
        [_perm(5, [[0, 1]]), _perm(5, [[0, 1, 2, 3, 4]])],                 # S5
        [_perm(9, [[0, 1, 2]]), _perm(9, [[0, 3, 6], [1, 4, 7], [2, 5, 8]])],  # Z3 wr Z3
        [_matrix_perm([[1, 1], [0, 1]]), _matrix_perm([[0, 1], [1, 0]]),
         _matrix_perm([[2, 0], [0, 1]])],                                  # GL(2,3)
    ]


def _pick_groups(lo, hi, d, rng):
    """Candidate groups with lo <= order <= hi, sorted by decreasing order (at most 60)."""
    bases = []
    for gens in _gens_list():
        r = _closure(gens, hi)
        if r is not None:
            bases.append(r)
    bases += [_semidirect_table(2, 1, 1), _semidirect_table(3, 1, 1)]
    fixed = []
    for X in bases:
        if lo <= X[0] <= hi:
            fixed.append(X)
        for j in range(2, hi // X[0] + 1):
            if lo <= X[0] * j <= hi:
                fixed.append(_direct(X, _semidirect_table(j, 1, 1)))
    sd = []
    for N in range(lo, hi + 1):
        for m in range(2, N + 1):
            if N % m:
                continue
            k = N // m
            for r in range(1, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    sd.append((m, k, r))
    rng.shuffle(sd)
    chosen = fixed + [_semidirect_table(*t) for t in sd[:30]]
    chosen = [g for g in chosen if g[0] >= d]
    if len(chosen) > 60:
        chosen = rng.sample(chosen, 60)
    chosen.sort(key=lambda t: -t[0])
    return chosen


def _run_group_search(d, D, seed, budget, groups):
    """Run the C search; return (n, edges) for a valid bi-Cayley graph, or None."""
    vals = [len(groups)]
    for N, flat in groups:
        vals.append(N)
        vals.extend(flat)
    if len(vals) % 2:
        vals.append(0)
    # run_c writes the pairs as "u v" lines; the C side reads the numbers in order.
    edges = list(zip(vals[0::2], vals[1::2]))
    out = lib.run_c(C_SOURCE, [d, D, seed, budget], stdin_graph=(0, edges),
                    timeout=budget + 6)
    toks = out.split()
    if not toks or toks[0] == "NONE" or len(toks) < 1 + d:
        return None
    gid = int(toks[0])
    S = [int(t) for t in toks[1:1 + d]]
    N, flat = groups[gid]
    # Vertex g on side 0 is g; vertex y on side 1 is N + y.
    out_edges = [(g, N + flat[g * N + s]) for g in range(N) for s in S]
    return 2 * N, out_edges


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        L = 2 * D
        return L, [(i, (i + 1) % L) for i in range(L)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}: always valid for D >= 2
    for cand in known_starts(d, D):
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    moore = lib.moore_bound(d, D)
    if d > 31 or best[0] >= moore:
        return best

    hi = min(moore // 2, 160)
    lo = max(d, min(hi, max(best[0] // 2 + 1, hi // 2)))
    if lo > hi:
        return best

    try:
        rng = random.Random(seed * 7919 + 13)
        groups = _pick_groups(lo, hi, d, rng)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        if groups and budget > 2.0:
            cand = _run_group_search(d, D, seed, budget, groups)
            if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
                best = cand
    except Exception:
        pass
    return best
