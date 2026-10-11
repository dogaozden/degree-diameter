import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Strategy
#
# 1. Exact Moore graphs where they exist (D = 3, d-1 a prime power: PG(2, d-1)).
# 2. Otherwise start from the best cheap construction: arc-extended projective
#    plane graphs (D = 3) or W(q) (D = 4), plus K_{d,d} as a safe fallback.
# 3. Hand that graph to a C engine that searches bi-Cayley voltage lifts over
#    semidirect products Z_m x| Z_k2 with k = 1..4 base vertices per side. It
#    uses simulated annealing with an exact cost (unreached pairs from one
#    representative per vertex orbit, plus a duplicate-edge penalty). Each
#    success is strictly larger than the previous best, so the search climbs.
# 4. Every returned graph is checked with lib.is_valid. If the C run fails for
#    any reason, the Python result is returned unchanged.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP 4000
#define KMAX 4
#define PENALTY 4

static int d, D, K, G, M, K2;
static long long RPOW[16];
static int *dI, *dJ, *dS;
static int *adj, *cnt, *stamp, *queue;
static int curstamp = 0;
static uint64_t rng_s = 1;

static uint64_t rnd64(void) {
    rng_s ^= rng_s >> 12;
    rng_s ^= rng_s << 25;
    rng_s ^= rng_s >> 27;
    return rng_s * 2685821657736338717ULL;
}

static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) { return (double)clock() / (double)CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* Semidirect product Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + r^b c, b+e). */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    long long t = ((long long)a + RPOW[b] * (long long)c) % M;
    int bb = (b + e) % K2;
    return (int)(t * K2 + bb);
}

static void setup_group(int m, int k2, int r) {
    M = m;
    K2 = k2;
    G = m * k2;
    RPOW[0] = 1 % m;
    for (int b = 1; b < k2; b++) RPOW[b] = (RPOW[b - 1] * r) % m;
}

static int find_r(int m, int k2) {
    if (k2 == 1) return 1 % m;
    for (int tries = 0; tries < 400; tries++) {
        int r = 1 + rndint(m - 1);
        if (gcd_i(r, m) != 1) continue;
        long long p = 1 % m;
        for (int t = 0; t < k2; t++) p = (p * r) % m;
        if (p == 1 % m) return r;
    }
    return 1 % m;
}

/* Cost = unreached pairs from orbit representatives + penalty for duplicate darts. */
static long long eval_cost(int N) {
    int dd = d * K;
    long long pen = 0;
    for (int a = 0; a < dd; a++)
        for (int b = a + 1; b < dd; b++)
            if (dI[a] == dI[b] && dJ[a] == dJ[b] && dS[a] == dS[b]) pen++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int idx = 0; idx < dd; idx++) {
        int i = dI[idx], j = dJ[idx], s = dS[idx];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + gmul(g, s);
            if (cnt[a] < d) adj[a * d + cnt[a]] = b;
            cnt[a]++;
            if (cnt[b] < d) adj[b * d + cnt[b]] = a;
            cnt[b]++;
        }
    }

    long long unreached = 0;
    for (int rr = 0; rr < 2 * K; rr++) {
        int src = (rr < K) ? rr * G : (K + (rr - K)) * G;
        curstamp++;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NCAP);
            curstamp = 1;
        }
        int head = 0, tail = 0;
        queue[tail++] = src;
        stamp[src] = curstamp;
        for (int depth = 0; depth < D && head < tail; depth++) {
            int end = tail;
            while (head < end) {
                int u = queue[head++];
                for (int t = 0; t < d; t++) {
                    int v = adj[u * d + t];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        queue[tail++] = v;
                    }
                }
            }
        }
        unreached += N - tail;
    }
    return unreached + (long long)PENALTY * pen;
}

static int anneal(int N, long long iters, double tlimit) {
    int dd = d * K;
    long long cur = eval_cost(N);
    double T = 2.0;
    const double decay = 0.99993;
    for (long long it = 0; it < iters; it++) {
        if (cur == 0) return 1;
        if ((it & 511) == 0 && now_s() > tlimit) break;
        if (K == 1 || rnd01() < 0.6) {
            int idx = rndint(dd);
            int old = dS[idx];
            int nw = rndint(G);
            if (nw == old) continue;
            dS[idx] = nw;
            long long c2 = eval_cost(N);
            long long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c2;
            else dS[idx] = old;
        } else {
            int L = rndint(d);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int a = L * K + i1, b = L * K + i2;
            int ta = dJ[a];
            dJ[a] = dJ[b];
            dJ[b] = ta;
            long long c2 = eval_cost(N);
            long long delta = c2 - cur;
            if (delta <= 0 || rnd01() < exp(-(double)delta / T)) cur = c2;
            else {
                ta = dJ[a];
                dJ[a] = dJ[b];
                dJ[b] = ta;
            }
        }
        T *= decay;
        if (T < 0.15) T = 0.15;
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long long seed = atoll(argv[3]);
    double tl = atof(argv[4]);
    rng_s = (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 0x632BE59BD9B4E019ULL;
    if (rng_s == 0) rng_s = 1;
    if (d < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0) { n0 = 0; m0 = 0; }
    int *e0 = malloc(sizeof(int) * 2 * (size_t)(m0 + 1));
    int read_ok = 1;
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &e0[2 * i], &e0[2 * i + 1]) != 2) {
            read_ok = 0;
            m0 = i;
            break;
        }
    }

    int best_n, best_m;
    int *best_e;
    if (read_ok && n0 >= 2 && m0 > 0) {
        best_n = n0;
        best_m = m0;
        best_e = e0;
    } else {
        free(e0);
        best_n = 2;
        best_m = 1;
        best_e = malloc(sizeof(int) * 2);
        best_e[0] = 0;
        best_e[1] = 1;
    }

    /* Bipartite Moore bound, as in lib._moore_bound. */
    double mbd;
    if (d == 1) mbd = 2.0;
    else if (d == 2) mbd = 2.0 * D;
    else {
        mbd = 0.0;
        double pw = 1.0;
        for (int i = 0; i < D && i < 60; i++) {
            mbd += pw;
            pw *= (double)(d - 1);
            if (mbd > 1e9) break;
        }
        mbd *= 2.0;
    }
    if (mbd > 1e9) mbd = 1e9;
    long long cap = (long long)mbd;
    if (cap > NCAP) cap = NCAP;

    if (best_n < cap) {
        dI = malloc(sizeof(int) * (size_t)d * KMAX);
        dJ = malloc(sizeof(int) * (size_t)d * KMAX);
        dS = malloc(sizeof(int) * (size_t)d * KMAX);
        adj = malloc(sizeof(int) * (size_t)NCAP * (size_t)d);
        cnt = malloc(sizeof(int) * NCAP);
        stamp = calloc(NCAP, sizeof(int));
        queue = malloc(sizeof(int) * NCAP);

        while (now_s() < tl) {
            int r = rndint(10);
            int kk = (r < 4) ? 1 : (r < 7) ? 2 : (r < 9) ? 3 : 4;
            long long Gmin = best_n / (2 * kk) + 1;
            long long Gmax = cap / (2 * kk);
            if (Gmin < 2) Gmin = 2;
            if (Gmax < Gmin) {
                kk = 1;
                Gmin = best_n / 2 + 1;
                if (Gmin < 2) Gmin = 2;
                Gmax = cap / 2;
                if (Gmax < Gmin) break;
            }
            long long span = Gmax - Gmin;
            if (span > 2) span = 2;
            int Gt = (int)(Gmin + rndint((int)span + 1));
            K = kk;

            int divs[32];
            int nd = 0;
            for (int q = 1; q <= 12 && q <= Gt; q++)
                if (Gt % q == 0 && Gt / q >= 2) divs[nd++] = q;
            int k2 = divs[rndint(nd)];
            int m = Gt / k2;
            int rr = find_r(m, k2);
            setup_group(m, k2, rr);

            int N = 2 * K * G;
            int dd = d * K;
            for (int L = 0; L < d; L++) {
                int perm[KMAX];
                for (int i = 0; i < K; i++) perm[i] = i;
                for (int i = K - 1; i > 0; i--) {
                    int j = rndint(i + 1);
                    int t = perm[i];
                    perm[i] = perm[j];
                    perm[j] = t;
                }
                for (int i = 0; i < K; i++) {
                    int idx = L * K + i;
                    dI[idx] = i;
                    dJ[idx] = perm[i];
                    dS[idx] = rndint(G);
                }
            }

            if (anneal(N, 80000, tl)) {
                int mm = dd * G;
                int *ne = malloc(sizeof(int) * 2 * (size_t)mm);
                int c = 0;
                for (int idx = 0; idx < dd; idx++) {
                    int i = dI[idx], j = dJ[idx], s = dS[idx];
                    for (int g = 0; g < G; g++) {
                        ne[2 * c] = i * G + g;
                        ne[2 * c + 1] = (K + j) * G + gmul(g, s);
                        c++;
                    }
                }
                if (N > best_n) {
                    free(best_e);
                    best_e = ne;
                    best_n = N;
                    best_m = mm;
                } else {
                    free(ne);
                }
            }
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
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


def _arc_graph(m, edges, point_lines, S, line_points):
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
        out.append(_arc_graph(m, edges, point_lines, S, line_points))
    return out


# ----------------------------------------------------------------------------
# Generalized quadrangle baseline (D = 4).
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
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d <= 0 or D <= 0:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]  # K2: valid for d >= 1, D >= 1

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, list(e))
            best_n = n

    # Moore graph: PG(2, d-1) is optimal for D = 3 when d-1 is a prime power.
    if D == 3 and lib.is_prime_power(d - 1):
        n, e = lib.projective_plane_incidence(d - 1)
        if lib.is_valid(n, e, d, D):
            return n, e

    # Cheap structured starts.
    try:
        arc_deadline = t0 + 0.2 * time_limit
        for n_c, e_c in _arc_extensions(d, arc_deadline, random.Random(seed * 7919 + d)):
            consider(n_c, e_c)
    except Exception:
        pass

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        try:
            gq = _best_gq(d)
            if gq is not None:
                consider(gq[0], gq[1])
        except Exception:
            pass

    # Main search in C, starting from the best valid graph found so far.
    remaining = time_limit - (time.monotonic() - t0)
    budget = 0.72 * remaining - 1.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
