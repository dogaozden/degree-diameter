"""Program for D = 3 bipartite degree-diameter graphs.

Approach:
  1. Python builds the best closed-form or arc-extended projective-plane graph it can.
  2. For D = 3 the C engine searches Haar graphs over groups G of order N, with
     N in [Nlo, d^2-d+1]. A Haar graph has vertices G x {0,1} and joins a_x to b_{x s}
     for s in S, |S| = d. If S S^{-1} = G, the graph has diameter 3. Such a cover
     exists only when N <= d^2-d+1, which gives order 2(d^2-d+1) = 482 for d = 16.
     The C side anneals over S, the groups are Z_m x| Z_k, and it returns the largest N found.
  3. Python keeps the best valid graph of all candidates. K_{d,d} is the fallback.
"""
import random
import time

import lib

C_SOURCE = r'''
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 1100
#define MAXD 64
#define MAXG 8192

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

/* Group Z_m x|_r Z_k, element a*k+b, identity 0. */
typedef struct { int m, k, r; } GDesc;
static GDesc gl[MAXG];
static int ng;

static void list_groups(int n) {
    ng = 0;
    for (int m = 1; m <= n; m++) {
        if (n % m) continue;
        int k = n / m;
        for (int r = 0; r < m; r++) {
            if (gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != (1 % m)) continue;
            if (ng < MAXG) { gl[ng].m = m; gl[ng].k = k; gl[ng].r = r; ng++; }
        }
    }
}

static int GN, GK, GM;
static int rp[MAXN];
static int invt[MAXN];

static inline int gm(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    return (int)(((long)a + (long)rp[b] * c) % GM) * GK + (b + e) % GK;
}

static int set_group(const GDesc *G) {
    GN = G->m * G->k;
    GM = G->m;
    GK = G->k;
    rp[0] = 1 % GM;
    for (int b = 1; b < GK; b++) rp[b] = (int)((long)rp[b - 1] * G->r % GM);
    for (int x = 0; x < GN; x++) {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        int ia = (int)((GM - ((long)rp[nb] * a) % GM) % GM);
        invt[x] = ia * GK + nb;
    }
    for (int x = 0; x < GN; x++)
        if (gm(x, invt[x]) != 0) return 0;
    return 1;
}

static int dd;
static int S[MAXD];
static unsigned char inS[MAXN];
static int cnt[MAXN];
static int uncov;

/* cnt[g] = number of ordered pairs (i != j) with s_i * s_j^{-1} = g. uncov = non-identity g with cnt 0. */
static void bump(int g, int delta) {
    if (g == 0) return;
    if (delta > 0) {
        if (cnt[g] == 0) uncov--;
        cnt[g]++;
    } else {
        cnt[g]--;
        if (cnt[g] == 0) uncov++;
    }
}

static void set_elem(int t, int x) {
    int o = S[t];
    for (int j = 0; j < dd; j++) {
        if (j == t) continue;
        bump(gm(o, invt[S[j]]), -1);
        bump(gm(S[j], invt[o]), -1);
    }
    inS[o] = 0;
    S[t] = x;
    inS[x] = 1;
    for (int j = 0; j < dd; j++) {
        if (j == t) continue;
        bump(gm(x, invt[S[j]]), 1);
        bump(gm(S[j], invt[x]), 1);
    }
}

static void init_state(void) {
    memset(cnt, 0, sizeof(int) * (size_t)GN);
    memset(inS, 0, (size_t)GN);
    uncov = GN - 1;
    for (int i = 0; i < dd; i++) {
        int x;
        do x = rndint(GN); while (inS[x]);
        S[i] = x;
        inS[x] = 1;
    }
    for (int i = 0; i < dd; i++)
        for (int j = 0; j < dd; j++)
            if (i != j) bump(gm(S[i], invt[S[j]]), 1);
}

static int anneal(long moves, double T0, double T1, double until) {
    init_state();
    double ratio = T1 / T0;
    double T = T0;
    for (long it = 0; it < moves && uncov > 0; it++) {
        if ((it & 1023) == 0) {
            if (now() > until) return 0;
            T = T0 * pow(ratio, (double)it / (double)moves);
        }
        int t = rndint(dd);
        int x;
        do x = rndint(GN); while (inS[x]);
        int o = S[t];
        int before = uncov;
        set_elem(t, x);
        int delta = uncov - before;
        if (delta > 0 && rnd01() >= exp(-delta / T)) set_elem(t, o);
    }
    return uncov == 0;
}

static void emit(void) {
    int n = 2 * GN;
    long E = (long)GN * dd;
    printf("%d %ld\n", n, E);
    for (int x = 0; x < GN; x++)
        for (int i = 0; i < dd; i++)
            printf("%d %d\n", x, GN + gm(x, S[i]));
}

int main(int argc, char **argv) {
    if (argc < 6) {
        fprintf(stderr, "usage: %s d D seed time_limit Nlo\n", argv[0]);
        return 2;
    }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int Nlo = atoi(argv[5]);
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    double t0 = now();
    double t_end = t0 + limit * 0.92;
    dd = d;
    if (D != 3 || d < 2 || d > MAXD) {
        printf("0 0\n");
        return 0;
    }
    int Nmax = d * d - d + 1;
    if (Nmax > MAXN - 1) Nmax = MAXN - 1;
    int Nmin = Nlo > d + 1 ? Nlo : d + 1;
    if (Nmin > Nmax) {
        printf("0 0\n");
        return 0;
    }
    for (int N = Nmax; N >= Nmin; N--) {
        double remain = t_end - now();
        if (remain <= 0) break;
        double slice_end = now() + remain / (double)(N - Nmin + 1);
        list_groups(N);
        int found = 0;
        while (!found && now() < slice_end) {
            const GDesc *G = &gl[rndint(ng)];
            if (!set_group(G)) continue;
            if (anneal(60000, 1.0, 0.05, slice_end)) found = 1;
        }
        if (found) {
            emit();
            return 0;
        }
    }
    printf("0 0\n");
    return 0;
}
'''


def _pg_data(q):
    """Points/lines of PG(2, q): point i and line i share the vector pts[i]."""
    pts = lib.projective_points(q)
    n2, edges = lib.projective_plane_incidence(q)
    m = n2 // 2
    point_lines = [[] for _ in range(m)]
    line_points = [[] for _ in range(m)]
    for u, v in edges:
        point_lines[u].append(v - m)
        line_points[v - m].append(u)
    index = {p: i for i, p in enumerate(pts)}
    return m, edges, point_lines, line_points, index


def _loads_ok(S, s, m, point_lines, line_points):
    """Every line holds <= s points of S and every point lies on <= s lines indexed by S."""
    cl = [0] * m
    cp = [0] * m
    for P in S:
        for L in point_lines[P]:
            cl[L] += 1
        for Q in line_points[P]:
            cp[Q] += 1
    return max(cl, default=0) <= s and max(cp, default=0) <= s


def _greedy_arc(m, s, point_lines, line_points, rng, trials, deadline):
    """Randomized greedy set S with all loads <= s; returns the largest found."""
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
    """Conic (plus nucleus for even q): an arc with no three collinear points."""
    S = [index[(1, t, F.mul(t, t))] for t in range(q)]
    S.append(index[(0, 0, 1)])
    if q % 2 == 0:
        S.append(index[(0, 1, 0)])
    return S


def _arc_graph(m, edges, point_lines, line_points, S):
    """Old PG(2,q) incidence plus, per element P of S, an A-vertex on the lines through P
    and a B-vertex on the points of line P. Diameter 3."""
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


def _arc_candidates(d, deadline, rng):
    """(n, edges) candidates from arc-extended projective planes, for each prime power q."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        if s < 1:
            continue
        m, edges, point_lines, line_points, index = _pg_data(q)
        cands = [_greedy_arc(m, s, point_lines, line_points, rng, 30, deadline)]
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if _loads_ok(cs, s, m, point_lines, line_points):
                cands.append(cs)
        S = max(cands, key=len)
        if not S or not _loads_ok(S, s, m, point_lines, line_points):
            continue
        out.append(_arc_graph(m, edges, point_lines, line_points, S))
    return out


def known_start(d, D):
    """Best closed-form graph for (d, D), or None."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1)   # Moore graph: optimal
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    if D == 2:
        return best

    def consider(cand):
        nonlocal best
        if cand is not None and cand[0] > best[0] and lib.is_valid(cand[0], cand[1], d, D):
            best = (cand[0], list(cand[1]))

    consider(known_start(d, D))
    rng = random.Random(seed * 7919 + d)
    for cand in sorted(_arc_candidates(d, t0 + 0.15 * time_limit, rng), key=lambda t: -t[0]):
        consider(cand)

    # D = 3: Haar-graph search over groups for orders above the current best side size.
    if D == 3:
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 1.0
        if budget > 1.0 and best[0] < lib.moore_bound(d, D):
            nlo = best[0] // 2 + 1
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), nlo],
                                 stdin_graph=None, timeout=budget + 5)
                n, e = lib.parse_graph_text(text)
                if n > best[0] and lib.is_valid(n, e, d, D):
                    best = (n, e)
            except (RuntimeError, ValueError):
                pass   # keep the construction if the search fails

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
