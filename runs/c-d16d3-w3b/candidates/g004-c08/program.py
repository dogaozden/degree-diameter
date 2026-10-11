import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley voltage lifts (any D >= 3).
#
# A lift is over a semidirect product Z_M x| Z_K2 (order G = M*K2) with K base
# vertices per side. Layer L is a permutation sigma_L of the K base indices
# (dart (L,i) joins A_i to B_sigma_L(i)), and each dart carries a voltage s:
# A_{i,g} is joined to B_{j, g*s}. The lift has 2*K*G vertices and degree d.
# Left translation is an automorphism, so the BFS cost only needs one source
# per base vertex. Cost = unreached (source, vertex) pairs + duplicate penalty.
# Cost 0 means a valid graph. Moves: change one voltage, or swap two targets
# within one layer. Simulated annealing runs repeatedly, growing G each time it
# succeeds, so the output always beats min_n. It prints "0 0" if nothing beats
# min_n.
# Args: d D seed time_limit [min_n] [cap]
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXD 32
#define MAXK 8
#define MAXG 4096
#define MAXN (2 * MAXK * MAXG)
#define MAXDART (MAXD * MAXK)
#define MAXE (MAXD * MAXK * MAXG)
#define PEN 20
#define ITERS 80000

static int d, D, K, G, K2, M;
static int pw[16];
static int jt[MAXDART];
static int st[MAXDART];
static int perm[MAXDART * MAXG];
static int adjv[MAXN][MAXD];
static int deg_[MAXN];
static int visit[MAXN];
static int stamp = 0;
static int queue_[MAXN];
static int bu[MAXE], bv[MAXE];
static int best_n = 0, best_m = 0;
static uint64_t rs = 88172645463325252ULL;
static double tl;
static clock_t t0;

static uint64_t xs(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int k) { return (int)(xs() % (uint64_t)k); }
static double rdbl(void) { return (double)(xs() >> 11) * (1.0 / 9007199254740992.0); }
static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long powmod_(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static int timed_out(void) {
    return (double)(clock() - t0) / CLOCKS_PER_SEC > tl;
}

/* perm for dart t: g -> g*s in Z_M x| Z_K2 */
static void set_perm(int t) {
    int c = st[t] / K2, e = st[t] % K2;
    int *p = &perm[t * MAXG];
    for (int g = 0; g < G; g++) {
        int a = g / K2, b = g % K2;
        p[g] = ((a + pw[b] * c) % M) * K2 + (b + e) % K2;
    }
}

static void choose_group(void) {
    int cands[16], nc = 0;
    for (int k2 = 1; k2 <= 12 && k2 <= G; k2++)
        if (G % k2 == 0) cands[nc++] = k2;
    K2 = cands[rint_(nc)];
    M = G / K2;
    int R = 1;
    if (K2 > 1 && rint_(10) < 7) {
        int cnt = 0;
        for (int r = 1; r < M; r++) {
            if (gcd_(r, M) == 1 && powmod_(r, K2, M) == (1 % M)) {
                cnt++;
                if (rint_(cnt) == 0) R = r;
            }
        }
    }
    pw[0] = 1 % M;
    for (int b = 1; b < K2; b++) pw[b] = (int)((long)pw[b - 1] * R % M);
}

static void randomize_state(void) {
    for (int L = 0; L < d; L++) {
        int p[MAXK];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) jt[L * K + i] = p[i];
    }
    for (int t = 0; t < d * K; t++) {
        st[t] = rint_(G);
        set_perm(t);
    }
}

static int dup_count(void) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int L1 = 0; L1 < d; L1++)
            for (int L2 = L1 + 1; L2 < d; L2++) {
                int t1 = L1 * K + i, t2 = L2 * K + i;
                if (jt[t1] == jt[t2] && st[t1] == st[t2]) dup++;
            }
    return dup;
}

static void build_adj(void) {
    int N = 2 * K * G;
    for (int v = 0; v < N; v++) deg_[v] = 0;
    for (int t = 0; t < d * K; t++) {
        int i = t % K, j = jt[t];
        int *p = &perm[t * MAXG];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = (K + j) * G + p[g];
            adjv[a][deg_[a]++] = b;
            adjv[b][deg_[b]++] = a;
        }
    }
}

static long eval_cost(void) {
    build_adj();
    int N = 2 * K * G;
    long total = 0;
    for (int x = 0; x < 2 * K; x++) {
        int src = x * G;
        stamp++;
        visit[src] = stamp;
        queue_[0] = src;
        int qh = 0, qt = 1;
        for (int lev = 0; lev < D; lev++) {
            int end = qt;
            if (qh == end) break;
            while (qh < end) {
                int u = queue_[qh++];
                for (int k = 0; k < d; k++) {
                    int v = adjv[u][k];
                    if (visit[v] != stamp) {
                        visit[v] = stamp;
                        queue_[qt++] = v;
                    }
                }
            }
        }
        total += N - qt;
    }
    return total + (long)PEN * dup_count();
}

static int anneal(long iters) {
    randomize_state();
    long cost = eval_cost();
    double T0 = 1.5, T1 = 0.05;
    for (long it = 0; it < iters && cost > 0; it++) {
        if ((it & 255) == 0 && timed_out()) return 0;
        double T = T0 * pow(T1 / T0, (double)it / (double)iters);
        if (K == 1 || rint_(2) == 0) {
            int t = rint_(d * K);
            int old = st[t];
            int nw = rint_(G);
            if (nw == old) continue;
            st[t] = nw;
            set_perm(t);
            long c2 = eval_cost();
            long delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                st[t] = old;
                set_perm(t);
            }
        } else {
            int L = rint_(d);
            int a = rint_(K), b = rint_(K - 1);
            if (b >= a) b++;
            int ta = L * K + a, tb = L * K + b;
            int tmp = jt[ta]; jt[ta] = jt[tb]; jt[tb] = tmp;
            long c2 = eval_cost();
            long delta = c2 - cost;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cost = c2;
            } else {
                tmp = jt[ta]; jt[ta] = jt[tb]; jt[tb] = tmp;
            }
        }
    }
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 977ULL);
    if (rs == 0) rs = 1;
    tl = atof(argv[4]);
    long min_n = argc > 5 ? atol(argv[5]) : 0;
    long cap = argc > 6 ? atol(argv[6]) : 1000000000L;
    t0 = clock();
    if (d < 1 || d > MAXD || D < 1) { printf("0 0\n"); return 0; }

    static const int ks[] = {1, 2, 3, 4, 5, 6, 8};
    int nk = 7;
    long bestn = min_n;
    int have = 0;
    long attempt = 0;
    while (!timed_out()) {
        if (bestn >= cap) break;
        int Kc = ks[attempt % nk];
        attempt++;
        long Gt = bestn / (2 * Kc) + 1;
        if (Gt < 2) Gt = 2;
        if (rint_(3) == 0) Gt += rint_(3);
        if (2 * Kc * Gt > cap) continue;
        if (Gt > MAXG) continue;
        if (d > Kc * Gt) continue;
        K = Kc;
        G = (int)Gt;
        choose_group();
        if (anneal(ITERS)) {
            bestn = 2L * K * G;
            best_n = (int)bestn;
            int m = 0;
            for (int t = 0; t < d * K; t++) {
                int i = t % K, j = jt[t];
                for (int g = 0; g < G; g++) {
                    bu[m] = i * G + g;
                    bv[m] = (K + j) * G + perm[t * MAXG + g];
                    m++;
                }
            }
            best_m = m;
            have = 1;
        }
    }
    if (!have) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_n, best_m);
    for (int i = 0; i < best_m; i++) printf("%d %d\n", bu[i], bv[i]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q). With d >= q+1 each vertex has
# spare capacity s = d - q - 1. Choose S so that every line holds <= s points
# of S and every point lies on <= s lines indexed by S. Add an A-vertex joined
# to the q+1 lines through each P in S, and a B-vertex joined to the q+1 points
# on each line j in S.
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 1.0
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(g):
        nonlocal best
        try:
            if g[0] > best[0] and lib.is_valid(g[0], g[1], d, D):
                best = (g[0], list(g[1]))
        except Exception:
            pass

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

    # Bi-Cayley voltage-lift search in C. It only looks for graphs larger than
    # the current best, and stops at the Moore bound.
    cap = lib.moore_bound(d, D)
    budget = end - time.monotonic()
    if best[0] < cap and budget > 3.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, round(budget - 1.0, 2), best[0], cap],
                            timeout=budget + 1.5)
            consider(lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best[0], list(best[1])
