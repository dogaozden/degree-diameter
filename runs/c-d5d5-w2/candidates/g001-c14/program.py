"""Bi-Cayley search over diverse finite groups (not only semidirect lifts).

Each group G of order N gives a bipartite graph on 2N vertices: A_x ~ B_{x s} for s in S,
where S is a set of d distinct group elements. Left multiplication is an automorphism that
preserves both sides, so the diameter check needs only two BFS runs (from A_e and B_e).
The C engine round-robins simulated annealing over the connection sets of all candidate
groups, largest order first, and stops improving once no larger group remains. Groups come
from permutation constructions (PGL(2,7), AGL(1,17), S_n, A_n, direct products with cyclic
groups) and sampled semidirect products. The known start graph (or K_{d,d}) is always kept
as a fallback.
"""
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

#define MAXD 32
#define MAXN 1024
#define MAXV (2 * MAXN)
#define MAXG 64
#define CHUNK 2000
#define STALL_LIMIT 60000L

typedef struct {
    int N, e;
    int *mt;      /* mt[x*N+y] = x*y */
    int *inv;     /* inverses */
    int S[MAXD], Si[MAXD];
    long cost;
    double T;
    long stall;
} Grp;

static int d, D;
static double t_end;
static Grp G[MAXG];
static int ng = 0;
static int vis[MAXV], qu[MAXV];
static int vstamp = 0;
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

static int in_set(const Grp *g, int s, int upto) {
    for (int i = 0; i < upto; i++)
        if (g->S[i] == s) return 1;
    return 0;
}

/* Number of (vertex, source) pairs left unreached within D steps from A_e and B_e. */
static long cost_of(const Grp *g) {
    int N = g->N, V = 2 * N;
    long unreached = 0;
    for (int src = 0; src < 2; src++) {
        vstamp++;
        int head = 0, tail = 0;
        int s0 = (src == 0) ? g->e : N + g->e;
        vis[s0] = vstamp;
        qu[tail++] = s0;
        for (int lev = 0; lev < D && head < tail; lev++) {
            int end = tail;
            while (head < end) {
                int u = qu[head++];
                if (u < N) {
                    const int *row = g->mt + (size_t)u * N;
                    for (int i = 0; i < d; i++) {
                        int v = N + row[g->S[i]];
                        if (vis[v] != vstamp) { vis[v] = vstamp; qu[tail++] = v; }
                    }
                } else {
                    const int *row = g->mt + (size_t)(u - N) * N;
                    for (int i = 0; i < d; i++) {
                        int v = row[g->Si[i]];
                        if (vis[v] != vstamp) { vis[v] = vstamp; qu[tail++] = v; }
                    }
                }
            }
        }
        unreached += V - tail;
    }
    return unreached;
}

static void set_state(Grp *g) {
    for (int i = 0; i < d; i++) {
        int s;
        do { s = rndint(g->N); } while (in_set(g, s, i));
        g->S[i] = s;
        g->Si[i] = g->inv[s];
    }
    g->cost = cost_of(g);
    g->T = 0.5 + 2.5 * rnd01();
    g->stall = 0;
}

static void run_chunk(Grp *g, int steps) {
    for (int it = 0; it < steps && g->cost > 0; it++) {
        int i = rndint(d);
        int s = rndint(g->N);
        if (in_set(g, s, d)) continue;
        int old = g->S[i], oldi = g->Si[i];
        g->S[i] = s;
        g->Si[i] = g->inv[s];
        long c2 = cost_of(g);
        if (c2 <= g->cost || rnd01() < exp(-(double)(c2 - g->cost) / g->T)) {
            if (c2 < g->cost) g->stall = 0; else g->stall++;
            g->cost = c2;
        } else {
            g->S[i] = old;
            g->Si[i] = oldi;
            g->stall++;
        }
        if (g->stall > STALL_LIMIT) set_state(g);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 2) { printf("0 0\n"); return 0; }

    /* Read every integer. Header "n m" is ignored; the payload is
       K, then per group: N e followed by N*N table entries (row-major). */
    size_t cap = 1 << 20, cnt = 0;
    long *tok = malloc(cap * sizeof(long));
    long x;
    while (scanf("%ld", &x) == 1) {
        if (cnt == cap) { cap *= 2; tok = realloc(tok, cap * sizeof(long)); }
        tok[cnt++] = x;
    }
    if (cnt < 3) { printf("0 0\n"); return 0; }

    long K = tok[2];
    size_t p = 3;
    for (long k = 0; k < K && ng < MAXG; k++) {
        if (p + 2 > cnt) break;
        long N = tok[p], e = tok[p + 1];
        p += 2;
        if (N < d || N > MAXN / 2 || e < 0 || e >= N) break;
        if (p + (size_t)(N * N) > cnt) break;
        Grp *g = &G[ng];
        g->N = (int)N;
        g->e = (int)e;
        g->mt = malloc(sizeof(int) * (size_t)(N * N));
        g->inv = malloc(sizeof(int) * (size_t)N);
        for (long i = 0; i < N * N; i++) {
            long v = tok[p + i];
            g->mt[i] = (v >= 0 && v < N) ? (int)v : 0;
        }
        p += (size_t)(N * N);
        int ok = 1;
        for (int a = 0; a < N && ok; a++) {
            g->inv[a] = -1;
            for (int b = 0; b < N; b++)
                if (g->mt[a * N + b] == g->e) { g->inv[a] = b; break; }
            if (g->inv[a] < 0) ok = 0;
        }
        if (ok) {
            set_state(g);
            ng++;
        } else {
            free(g->mt);
            free(g->inv);
        }
    }

    /* Groups are supplied largest first. Round-robin annealing; a group only
       matters while its graph (2N vertices) would beat the best found so far. */
    int bestN = 0, bestG = -1;
    while (now() < t_end) {
        int active = 0;
        for (int gi = 0; gi < ng && now() < t_end; gi++) {
            Grp *g = &G[gi];
            if (2 * g->N <= bestN) continue;
            active = 1;
            run_chunk(g, CHUNK);
            if (g->cost == 0) {
                bestN = 2 * g->N;
                bestG = gi;
            }
        }
        if (!active) break;
    }

    if (bestG < 0) { printf("0 0\n"); return 0; }
    Grp *g = &G[bestG];
    int N = g->N;
    printf("%d %d\n", 2 * N, N * d);
    for (int a = 0; a < N; a++)
        for (int i = 0; i < d; i++)
            printf("%d %d\n", a, N + g->mt[a * N + g->S[i]]);
    return 0;
}
'''


def _known_start(d, D):
    """Best directly constructible graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)           # record family 2(q^2+q+5)
    return None


# ----------------------------------------------------------- group constructions

def _prim_root(p):
    """A primitive root modulo the prime p."""
    primes = [q for q in range(2, p) if (p - 1) % q == 0
              and all(q % r for r in range(2, int(q ** 0.5) + 1))]
    for g in range(2, p):
        if all(pow(g, (p - 1) // q, p) != 1 for q in primes):
            return g
    return 1


def _cyc(n, cycles):
    """Permutation of range(n) given by disjoint cycles (tuples of points)."""
    perm = list(range(n))
    for c in cycles:
        for i, x in enumerate(c):
            perm[x] = c[(i + 1) % len(c)]
    return tuple(perm)


def _sym_gens(n):
    return [_cyc(n, [(0, 1)]), _cyc(n, [tuple(range(n))])]


def _alt_gens(n):
    return [_cyc(n, [(i, i + 1, i + 2)]) for i in range(n - 2)]


def _pgl2_gens(p):
    """PGL(2,p) acting on the projective line; point p is infinity."""
    g = _prim_root(p)
    t = tuple([(x + 1) % p for x in range(p)] + [p])
    m = tuple([(g * x) % p for x in range(p)] + [p])
    j = tuple([p if x == 0 else (-pow(x, p - 2, p)) % p for x in range(p)] + [0])
    return [t, m, j]


def _agl1_gens(p):
    """AGL(1,p): affine maps x -> a x + b on F_p."""
    g = _prim_root(p)
    t = tuple((x + 1) % p for x in range(p))
    m = tuple((g * x) % p for x in range(p))
    return [t, m]


def _closure(gens, limit):
    """Elements of the permutation group generated by gens (identity first), or None if above limit."""
    P = len(gens[0])
    ident = tuple(range(P))
    elems = [ident]
    idx = {ident: 0}
    i = 0
    while i < len(elems):
        a = elems[i]
        i += 1
        for g in gens:
            b = tuple(a[x] for x in g)
            if b not in idx:
                if len(elems) >= limit:
                    return None
                idx[b] = len(elems)
                elems.append(b)
    return elems


def _table(elems):
    """Multiplication table (row-major) of a permutation group given by its element list."""
    idx = {e: i for i, e in enumerate(elems)}
    mt = [idx[tuple(a[x] for x in b)] for a in elems for b in elems]
    return len(elems), mt


def _times_cyclic(N, mt, k):
    """Direct product of a group table (order N) with Z_k; identity stays index 0."""
    M = N * k
    out = [0] * (M * M)
    for g1 in range(N):
        for c1 in range(k):
            base_x = (g1 * k + c1) * M
            for g2 in range(N):
                r = mt[g1 * N + g2] * k
                for c2 in range(k):
                    out[base_x + g2 * k + c2] = r + (c1 + c2) % k
    return M, out


def _semidirect_specs(lo, hi):
    specs = []
    for N in range(lo, hi + 1):
        for m in range(2, N + 1):
            if N % m:
                continue
            k = N // m
            if k < 2:
                continue
            for r in range(2, m):
                if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m:
                    specs.append((m, k, r))
    return specs


def _groups(lo, hi, seed):
    """Candidate groups with lo <= order <= hi, as (N, mt), largest order first."""
    if lo > hi:
        return []
    out = []
    bases = [_pgl2_gens(7), _agl1_gens(17), _sym_gens(5), _alt_gens(5),
             _pgl2_gens(5), _sym_gens(4), _alt_gens(4)]
    for gens in bases:
        el = _closure(gens, hi + 1)
        if el is None:
            continue
        N0, mt0 = _table(el)
        for k in range(1, hi // N0 + 1):
            N = N0 * k
            if N < lo:
                continue
            if k == 1:
                out.append((N0, mt0))
            else:
                out.append(_times_cyclic(N0, mt0, k))
    rng = random.Random(seed)
    specs = _semidirect_specs(lo, hi)
    for m, k, r in rng.sample(specs, min(8, len(specs))):
        order, mul, _ = lib.semidirect_group(m, k, r)
        mt = [mul(x, y) for x in range(order) for y in range(order)]
        out.append((order, mt))
    out.sort(key=lambda t: -t[0])
    return out[:40]


def _pack(groups):
    """Encode groups as a graph text payload: the integers are sent as edge pairs."""
    payload = [len(groups)]
    for N, mt in groups:
        payload += [N, 0] + mt
    if len(payload) % 2:
        payload.append(0)
    edges = [(payload[i], payload[i + 1]) for i in range(0, len(payload), 2)]
    return (0, edges)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return (1, [])
    if D == 1:
        return (2, [(0, 1)])

    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = cand

    start = _known_start(d, D)
    if start is not None:
        consider(start)

    moore = lib.moore_bound(d, D)
    if best[0] >= moore:
        return best

    lo = best[0] // 2 + 1                 # groups that would beat the current best
    hi = min(moore // 2, 480)
    try:
        groups = _groups(lo, hi, seed)
    except (ValueError, ZeroDivisionError):
        groups = []
    if not groups:
        return best

    budget = 0.75 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best

    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=_pack(groups), timeout=budget + 10)
        consider(lib.parse_graph_text(text))
    except (RuntimeError, ValueError):
        pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
