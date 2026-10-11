import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bipartite Haar-type lifts over finite groups (diameter 3).
#
# Group G of order g = |G| and connection set S of size d give the bipartite
# graph with vertices a_x, b_y (x, y in G) and edges a_x -- b_{x s} for s in S.
# It is d-regular and bipartite. Distances are at most 3 exactly when
#   S S^{-1} = G  (covers a-a pairs and, with S S^{-1} S = G, the a-b pairs)
#   S^{-1} S = G  (covers b-b pairs).
# Order 2|G| with |G| <= d(d-1)+1, so |G| near 200 for d = 16 beats 394.
#
# The engine simulated-anneals S inside many groups (cyclic and Z_m x| Z_k)
# round-robin. Cost = uncovered elements of both covers. Groups with order
# above the best found so far stay active. It prints the largest valid graph.
# ----------------------------------------------------------------------------

C_HAAR = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXGRP 160
#define MAXD 64
#define MAXG 1200
#define TABMAX 400
#define CHUNK 500
#define CYC 200000L

typedef struct {
    long m, k, r, G;
    long *pw;
} Grp;

typedef struct {
    Grp g;
    uint16_t *tab;
    long *ivt;
    int *S;
    unsigned char *inS;
    int *mk1;
    int *mk2;
    int stamp;
    int cost;
    long it;
    int alive;
} St;

static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static long rint_(long k) { return (long)(rnd() % (uint64_t)k); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static long gcd_l(long a, long b) {
    while (b) { long t = a % b; a = b; b = t; }
    return a;
}

/* (a,b)(c,e) = (a + r^b c, b + e), element code a*k + b */
static long gmul(const Grp *g, long x, long y) {
    long a = x / g->k, b = x % g->k;
    long c = y / g->k, e = y % g->k;
    long A = (a + g->pw[b] * c) % g->m;
    long B = (b + e) % g->k;
    return A * g->k + B;
}

static long ginv(const Grp *g, long x) {
    long a = x / g->k, b = x % g->k;
    long nb = (g->k - b) % g->k;
    long A = (g->m - (g->pw[nb] * a) % g->m) % g->m;
    return A * g->k + nb;
}

static inline long mulx(const St *s, long x, long y) {
    if (s->tab) return (long)s->tab[x * s->g.G + y];
    return gmul(&s->g, x, y);
}

static int eval_cost(St *s, int d) {
    long G = s->g.G;
    long inv[MAXD];
    for (int i = 0; i < d; i++) inv[i] = s->ivt[s->S[i]];
    if (s->stamp >= 2000000000) {
        memset(s->mk1, 0, sizeof(int) * (size_t)G);
        memset(s->mk2, 0, sizeof(int) * (size_t)G);
        s->stamp = 0;
    }
    s->stamp++;
    int tag = s->stamp;
    for (int i = 0; i < d; i++) {
        for (int j = 0; j < d; j++) {
            long x = mulx(s, s->S[i], inv[j]);
            s->mk1[x] = tag;
            long y = mulx(s, inv[i], s->S[j]);
            s->mk2[y] = tag;
        }
    }
    int unc = 0;
    for (long x = 0; x < G; x++) {
        if (s->mk1[x] != tag) unc++;
        if (s->mk2[x] != tag) unc++;
    }
    return unc;
}

static void init_state(St *s, Grp g, int d) {
    long G = g.G;
    memset(s, 0, sizeof(*s));
    s->g = g;
    s->ivt = malloc(sizeof(long) * (size_t)G);
    for (long x = 0; x < G; x++) s->ivt[x] = ginv(&s->g, x);
    if (G <= TABMAX) {
        s->tab = malloc(sizeof(uint16_t) * (size_t)(G * G));
        for (long x = 0; x < G; x++)
            for (long y = 0; y < G; y++)
                s->tab[x * G + y] = (uint16_t)gmul(&s->g, x, y);
    }
    s->S = malloc(sizeof(int) * (size_t)d);
    s->inS = calloc((size_t)G, 1);
    s->mk1 = calloc((size_t)G, sizeof(int));
    s->mk2 = calloc((size_t)G, sizeof(int));
    for (int i = 0; i < d; i++) {
        long e;
        do { e = rint_(G); } while (s->inS[e]);
        s->inS[e] = 1;
        s->S[i] = (int)e;
    }
    s->alive = 1;
    s->cost = eval_cost(s, d);
}

static void step(St *s, int d) {
    long G = s->g.G;
    int i = (int)rint_(d);
    long e;
    do { e = rint_(G); } while (s->inS[e]);
    int old = s->S[i];
    s->inS[old] = 0;
    s->inS[e] = 1;
    s->S[i] = (int)e;
    int nc = eval_cost(s, d);
    int delta = nc - s->cost;
    double ph = (double)(s->it % CYC) / (double)CYC;
    double T = 0.05 + 1.2 * (1.0 - ph) * (1.0 - ph);
    s->it++;
    if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
        s->cost = nc;
    } else {
        s->inS[e] = 0;
        s->inS[old] = 1;
        s->S[i] = old;
    }
}

int main(int argc, char **argv) {
    if (argc < 6) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    const char *spec = argv[5];
    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    clock_t t0 = clock();

    St *st = calloc(MAXGRP, sizeof(St));
    int ng = 0;
    const char *p = spec;
    while (ng < MAXGRP && *p) {
        long m, k, r;
        int c = 0;
        if (sscanf(p, "%ld,%ld,%ld%n", &m, &k, &r, &c) != 3 || c <= 0) break;
        p += c;
        if (*p == ';') p++;
        if (k == 1) r = 1;
        if (m < 2 || k < 1 || m * k > MAXG || m * k <= d) continue;
        r %= m;
        if (r < 1 || gcd_l(r, m) != 1) continue;
        Grp g;
        g.m = m;
        g.k = k;
        g.r = r;
        g.G = m * k;
        g.pw = malloc(sizeof(long) * (size_t)k);
        g.pw[0] = 1 % m;
        for (long b = 1; b < k; b++) g.pw[b] = g.pw[b - 1] * r % m;
        if (g.pw[k - 1] * r % m != 1 % m) { free(g.pw); continue; }
        init_state(&st[ng], g, d);
        ng++;
    }

    int bestG = 0, bestIdx = -1;
    int bestS[MAXD];
    for (;;) {
        int any = 0;
        for (int gi = 0; gi < ng; gi++) {
            St *s = &st[gi];
            if (!s->alive || s->g.G <= bestG) continue;
            any = 1;
            for (int c = 0; c < CHUNK && s->cost > 0; c++) step(s, d);
            if (s->cost == 0) {
                bestG = (int)s->g.G;
                bestIdx = gi;
                memcpy(bestS, s->S, sizeof(int) * (size_t)d);
            }
        }
        if (!any) break;
        double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
        if (el > tl) break;
    }

    if (bestG <= 0) { printf("0 0\n"); return 0; }
    Grp *g = &st[bestIdx].g;
    long G = g->G;
    printf("%ld %ld\n", 2 * G, G * (long)d);
    for (long x = 0; x < G; x++)
        for (int i = 0; i < d; i++)
            printf("%ld %ld\n", x, G + gmul(g, x, (long)bestS[i]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
# ----------------------------------------------------------------------------

def _pg_data(q):
    """Return (m, edges, point_lines, line_points, index, pts) for PG(2, q)."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index, pts


def _loads_ok(S, s, m, point_lines, line_points):
    """True if every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy choice of S with all loads <= s; returns the largest found."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        cl = [0] * m
        cp = [0] * m
        S = []
        for P in order:
            if all(cl[L] < s for L in point_lines[P]) and all(cp[Q] < s for Q in line_points[P]):
                S.append(P)
                for L in point_lines[P]:
                    cl[L] += 1
                for Q in line_points[P]:
                    cp[Q] += 1
        if len(S) > len(best):
            best = S
    return best


def _conic_set(q, index, F):
    """Conic (plus nucleus for even q) as a point-index set: an arc with no three collinear."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG incidence plus a new A and a new B vertex per element of S."""
    k = len(S)
    n = 2 * m + 2 * k
    E = list(edges)
    for t, P in enumerate(S):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(S):
        b = 2 * m + k + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Return (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)
        cands = []
        if s >= 1:
            cands.append(_greedy_arc(m, s, point_lines, line_points, rng, 40, deadline))
        if s >= 2:
            F = lib.GF(q)
            cs = _conic_set(q, index, F)
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len, default=[])
        if not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle W(q) (diameter 4), used for D >= 4.
# ----------------------------------------------------------------------------

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
# Simulated annealing over bi-Cayley voltage lifts (used for D >= 4).
# ----------------------------------------------------------------------------

_BIG = 10 ** 9


def _sample_group(G, rng):
    """Return (order, mul) for a random semidirect product Z_m x| Z_k2 of order G, or None."""
    for _ in range(80):
        k2 = rng.choice([1, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12])
        if G % k2:
            continue
        m = G // k2
        if m < 2:
            continue
        if k2 == 1:
            r = 1
        else:
            cands = [r for r in rng.sample(range(1, m), min(m - 1, 60))
                     if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
            if not cands:
                continue
            r = rng.choice(cands)
        try:
            order, mul, _ = lib.semidirect_group(m, k2, r)
        except ValueError:
            continue
        return order, mul
    return None


def _right_perm(mul, G, s):
    """Permutation g -> mul(g, s) of the group."""
    return [mul(g, s) for g in range(G)]


def _cost(k, G, D, darts, perms):
    """Number of (representative, vertex) pairs not reached within distance D. Zero means valid."""
    if len({(i, j, s) for i, j, s in darts}) < len(darts):
        return _BIG
    N = 2 * k * G
    adj = [[] for _ in range(N)]
    for (i, j, _s), pm in zip(darts, perms):
        base_a = i * G
        base_b = (k + j) * G
        for g in range(G):
            a = base_a + g
            b = base_b + pm[g]
            adj[a].append(b)
            adj[b].append(a)
    reps = [i * G for i in range(k)] + [(k + j) * G for j in range(k)]
    total = 0
    for src in reps:
        seen = [False] * N
        seen[src] = True
        frontier = [src]
        count = 1
        for _ in range(D):
            nxt = []
            for u in frontier:
                for v in adj[u]:
                    if not seen[v]:
                        seen[v] = True
                        nxt.append(v)
            count += len(nxt)
            frontier = nxt
            if not frontier:
                break
        total += N - count
    return total


def _edges(k, G, darts, perms):
    E = set()
    for (i, j, _s), pm in zip(darts, perms):
        for g in range(G):
            E.add((i * G + g, (k + j) * G + pm[g]))
    return 2 * k * G, sorted(E)


def _anneal(d, D, k, G, mul, rng, deadline, iters):
    """Simulated annealing over voltages and per-layer B-assignments."""
    darts = []
    for _ in range(d):
        p = rng.sample(range(k), k)
        for i in range(k):
            darts.append([i, p[i], rng.randrange(G)])
    perms = [_right_perm(mul, G, s) for _, _, s in darts]
    cost = _cost(k, G, D, darts, perms)

    T = 1.0
    for _ in range(iters):
        if cost == 0 or time.monotonic() > deadline:
            break
        T = max(0.05, T * 0.997)

        if rng.random() < 0.7 or k == 1:
            idx = rng.randrange(len(darts))
            old_s = darts[idx][2]
            new_s = rng.randrange(G)
            if new_s == old_s:
                continue
            old_perm = perms[idx]
            darts[idx][2] = new_s
            perms[idx] = _right_perm(mul, G, new_s)
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[idx][2] = old_s
                perms[idx] = old_perm
        else:
            L = rng.randrange(d)
            a, b = rng.sample(range(k), 2)
            ia, ib = L * k + a, L * k + b
            darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]
            c2 = _cost(k, G, D, darts, perms)
            delta = c2 - cost
            if delta <= 0 or rng.random() < math.exp(-delta / T):
                cost = c2
            else:
                darts[ia][1], darts[ib][1] = darts[ib][1], darts[ia][1]

    if cost == 0:
        return _edges(k, G, darts, perms)
    return None


# ----------------------------------------------------------------------------
# Group specifications for the Haar-type search (D = 3).
# ----------------------------------------------------------------------------

def _group_specs(lo, hi, rng, cap):
    """List of (m, k, r) describing groups Z_m x| Z_k of orders lo..hi, largest order first."""
    specs = []
    for G in range(hi, lo - 1, -1):
        cand = []
        for k in range(1, G + 1):
            if G % k:
                continue
            m = G // k
            if m < 2:
                continue
            if k == 1:
                rs_ = [1]
            else:
                rs_ = [r for r in range(1, m)
                       if math.gcd(r, m) == 1 and pow(r, k, m) == 1 % m]
                rng.shuffle(rs_)
                rs_ = rs_[:2]
                if not rs_:
                    continue
            for r in rs_:
                cand.append((m, k, r))
        rng.shuffle(cand)
        specs.extend(cand[:2])
        if len(specs) >= cap:
            break
    return specs[:cap]


# ----------------------------------------------------------------------------
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 1.5
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
            best = (g[0], g[1])

    # Arc-extended projective plane graphs (valid for D >= 3).
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Bold change for D = 3: Haar-type lifts over groups, with S a difference cover.
    # Order 2|G| with |G| <= d(d-1)+1. Only orders that beat the current best are searched.
    if D == 3 and d >= 2:
        hi = min(1 + d * (d - 1), 1100)
        lo = max(best[0] // 2 + 1, d + 1)
        budget = end - time.monotonic() - 1.0
        if lo <= hi and budget > 2.0:
            specs = _group_specs(lo, hi, rng, cap=60)
            if specs:
                text = ";".join(f"{m},{k},{r}" for m, k, r in specs)
                try:
                    out = lib.run_c(C_HAAR, [d, D, seed, round(budget, 2), text],
                                    timeout=budget + 10)
                    consider(lib.parse_graph_text(out))
                except Exception:
                    pass

    # Voltage-lift annealing for D >= 4.
    if D >= 4:
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < end:
            k = rng.choice(ks)
            base = best[0] // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, end, iters=400)
            if res is not None:
                consider(res)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
