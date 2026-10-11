import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3).
#
# Start from the incidence graph of PG(2, q) (points 0..m-1, lines m..2m-1).
# Every old vertex has degree q+1, so with d >= q+1 it has spare s = d - q - 1.
#
# A-side: a set SA of points. Each SA point P gets a new vertex joined to all
#         q+1 lines through P. Constraint: every line holds <= s points of SA.
# B-side: a set SB of lines. Each j in SB gets a new vertex joined to all
#         q+1 points on j. Constraint: every point lies on <= s lines of SB.
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


def _loads_ok(S, s, m, nbr):
    """True if every target t is hit by <= s elements of S, where element x hits nbr[x]."""
    load = [0] * m
    for x in S:
        for t in nbr[x]:
            load[t] += 1
    return max(load, default=0) <= s


def _greedy_side(m, s, nbr, rng, trials, deadline):
    """Randomized greedy: choose elements x so that every target is hit by <= s chosen elements."""
    best = []
    order = list(range(m))
    for _ in range(trials):
        if time.monotonic() > deadline:
            break
        rng.shuffle(order)
        load = [0] * m
        S = []
        for x in order:
            if all(load[t] < s for t in nbr[x]):
                S.append(x)
                for t in nbr[x]:
                    load[t] += 1
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


def _arc_graph(m, edges, point_lines, line_points, SA, SB):
    """Old PG incidence plus one new A-vertex per SA point and one new B-vertex per SB line."""
    na, nb = len(SA), len(SB)
    n = 2 * m + na + nb
    E = list(edges)
    for t, P in enumerate(SA):
        x = 2 * m + t
        for L in point_lines[P]:
            E.append((x, m + L))
    for t, j in enumerate(SB):
        b = 2 * m + na + t
        for Q in line_points[j]:
            E.append((Q, b))
    return n, E


def _arc_extensions(d, deadline, rng):
    """Yield (n, edges) candidates for each prime power q with q + 1 <= d."""
    out = []
    for q in range(2, min(d - 1, 23) + 1):
        if not lib.is_prime_power(q):
            continue
        if time.monotonic() > deadline:
            break
        s = d - q - 1
        m, edges, point_lines, line_points, index, pts = _pg_data(q)

        SA = _greedy_side(m, s, point_lines, rng, 40, deadline)
        SB = _greedy_side(m, s, line_points, rng, 40, deadline)
        if s >= 2:
            cs = _conic_set(q, index, lib.GF(q))
            if len(cs) > len(SA) and _loads_ok(cs, s, m, point_lines):
                SA = cs
            if len(cs) > len(SB) and _loads_ok(cs, s, m, line_points):
                SB = cs

        if not (_loads_ok(SA, s, m, point_lines) and _loads_ok(SB, s, m, line_points)):
            continue
        n_c, e_c = _arc_graph(m, edges, point_lines, line_points, SA, SB)
        out.append((n_c, e_c))
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
# Simulated annealing over bi-Cayley voltage lifts (Python fallback for D >= 4).
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
# New search: C vertex-extension annealer.
#
# The engine keeps a bipartite graph with max degree d, a fixed side for every
# vertex, and an SA state whose cost is the number of vertex pairs at distance
# > D. Degree-preserving moves (double edge swaps), endpoint shifts that move a
# free slot onto a deficient vertex, and adds between deficient pairs explore
# the state space. Whenever the cost reaches 0 the graph gets one more vertex
# (random side) and the search continues. The best valid graph is printed.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define NCAP_MAX 4000
#define LOG_MAX 64

static int DEGMAX, DIAM;
static int NCAP, WCAP, N, W, EM;
static int *side_, *deg_, *nbr_, *ea_, *eb_, *d0_, *d1_;
static unsigned char *adjm_;
static uint64_t *bufA_, *bufB_;
static int best_N = 0, best_M = 0, have_best = 0;
static int *best_ea_, *best_eb_;
static int logop_[LOG_MAX], loga_[LOG_MAX], logb_[LOG_MAX];
static int nlog_ = 0, logging_ = 0;
static uint64_t rs_ = 88172645463325252ULL;
static clock_t t0_;
static double tlim_;

#define ADJ(u, v) adjm_[(size_t)(u) * (size_t)NCAP + (size_t)(v)]
#define NB(u, k) nbr_[(size_t)(u) * (size_t)DEGMAX + (size_t)(k)]

static uint64_t rnd_u64(void) {
    rs_ ^= rs_ >> 12;
    rs_ ^= rs_ << 25;
    rs_ ^= rs_ >> 27;
    return rs_ * 2685821657736338717ULL;
}
static int rnd_int(int n) { return (int)(rnd_u64() % (uint64_t)n); }
static double rnd_d(void) { return (double)(rnd_u64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0_) / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void raw_add(int u, int v) {
    if (side_[u] == 1) { int t = u; u = v; v = t; }
    NB(u, deg_[u]) = v; deg_[u]++;
    NB(v, deg_[v]) = u; deg_[v]++;
    ADJ(u, v) = 1; ADJ(v, u) = 1;
    ea_[EM] = u; eb_[EM] = v; EM++;
}

static void raw_rem(int u, int v) {
    int k;
    if (side_[u] == 1) { int t = u; u = v; v = t; }
    for (k = 0; k < deg_[u]; k++) if (NB(u, k) == v) break;
    if (k < deg_[u]) { NB(u, k) = NB(u, deg_[u] - 1); deg_[u]--; }
    for (k = 0; k < deg_[v]; k++) if (NB(v, k) == u) break;
    if (k < deg_[v]) { NB(v, k) = NB(v, deg_[v] - 1); deg_[v]--; }
    ADJ(u, v) = 0; ADJ(v, u) = 0;
    for (k = 0; k < EM; k++) {
        if (ea_[k] == u && eb_[k] == v) {
            ea_[k] = ea_[EM - 1]; eb_[k] = eb_[EM - 1]; EM--;
            break;
        }
    }
}

static void log_op(int op, int u, int v) {
    if (logging_ && nlog_ < LOG_MAX) {
        logop_[nlog_] = op; loga_[nlog_] = u; logb_[nlog_] = v; nlog_++;
    }
}
static void L_add(int u, int v) { raw_add(u, v); log_op(0, u, v); }
static void L_rem(int u, int v) { raw_rem(u, v); log_op(1, u, v); }

static void undo(void) {
    int was = logging_;
    logging_ = 0;
    while (nlog_ > 0) {
        nlog_--;
        if (logop_[nlog_] == 0) raw_rem(loga_[nlog_], logb_[nlog_]);
        else raw_add(loga_[nlog_], logb_[nlog_]);
    }
    logging_ = was;
}

/* Number of ordered-pair-free bad vertex pairs (distance > DIAM), each pair once. */
static long long evalcost(void) {
    uint64_t *cur = bufA_, *nxt = bufB_, *tmp;
    int v, r, k, i;
    for (v = 0; v < N; v++) {
        uint64_t *row = cur + (size_t)v * WCAP;
        for (k = 0; k < W; k++) row[k] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (r = 0; r < DIAM; r++) {
        for (v = 0; v < N; v++) {
            uint64_t *dst = nxt + (size_t)v * WCAP;
            uint64_t *src = cur + (size_t)v * WCAP;
            for (k = 0; k < W; k++) dst[k] = src[k];
            for (i = 0; i < deg_[v]; i++) {
                uint64_t *s2 = cur + (size_t)NB(v, i) * WCAP;
                for (k = 0; k < W; k++) dst[k] |= s2[k];
            }
        }
        tmp = cur; cur = nxt; nxt = tmp;
    }
    long long bad = 0;
    for (v = 0; v < N; v++) {
        int c = 0;
        uint64_t *row = cur + (size_t)v * WCAP;
        for (k = 0; k < W; k++) c += popc(row[k]);
        bad += N - c;
    }
    return bad / 2;
}

static int propose(void) {
    int nd0 = 0, nd1 = 0, v, i;
    for (v = 0; v < N; v++) {
        if (deg_[v] < DEGMAX) {
            if (side_[v] == 0) d0_[nd0++] = v;
            else d1_[nd1++] = v;
        }
    }
    double r = rnd_d();
    if (nd0 > 0 && nd1 > 0 && r < 0.3) {
        for (i = 0; i < 30; i++) {
            int x = d0_[rnd_int(nd0)], y = d1_[rnd_int(nd1)];
            if (!ADJ(x, y)) { L_add(x, y); return 1; }
        }
    }
    if (EM == 0) return 0;
    if (r < 0.65) {
        if (nd0 == 0 && nd1 == 0) return 0;
        int e = rnd_int(EM);
        int a = ea_[e], b = eb_[e];
        if (rnd_int(2) == 0) {
            if (nd0 == 0) return 0;
            int x = d0_[rnd_int(nd0)];
            if (x == a || ADJ(x, b)) return 0;
            L_rem(a, b); L_add(x, b);
            return 1;
        } else {
            if (nd1 == 0) return 0;
            int y = d1_[rnd_int(nd1)];
            if (y == b || ADJ(a, y)) return 0;
            L_rem(a, b); L_add(a, y);
            return 1;
        }
    }
    if (EM < 2) return 0;
    for (i = 0; i < 8; i++) {
        int e1 = rnd_int(EM), e2 = rnd_int(EM);
        if (e1 == e2) continue;
        int a = ea_[e1], b = eb_[e1], c = ea_[e2], dd = eb_[e2];
        if (a == c || b == dd) continue;
        if (ADJ(a, dd) || ADJ(c, b)) continue;
        L_rem(a, b); L_rem(c, dd);
        L_add(a, dd); L_add(c, b);
        return 1;
    }
    return 0;
}

static void save_best(void) {
    int i;
    best_N = N; best_M = EM; have_best = 1;
    for (i = 0; i < EM; i++) { best_ea_[i] = ea_[i]; best_eb_[i] = eb_[i]; }
}

static void load_edges(int n, int m, const int *xa, const int *xb) {
    int i;
    while (EM > 0) raw_rem(ea_[EM - 1], eb_[EM - 1]);
    N = n;
    for (i = 0; i < m; i++) raw_add(xa[i], xb[i]);
}

int main(int argc, char **argv) {
    int n0 = 0, m0 = 0, i, v, k;
    int *xa, *xb, *col, *tdeg;
    int empty_in = 0, bad = 0, found = -1;
    long long cur;
    int moves = 0;
    const int MAXMOVES = 50000;
    const double Tmax = 2.0, Tmin = 0.08;

    if (argc < 5) return 1;
    DEGMAX = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    rs_ = (uint64_t)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs_ == 0) rs_ = 1;
    tlim_ = atof(argv[4]);
    t0_ = clock();
    if (DEGMAX < 1 || DIAM < 2) { printf("0 0\n"); return 0; }

    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 <= 0 || m0 < 0) empty_in = 1;
    if (empty_in) { n0 = 2 * DEGMAX; m0 = DEGMAX * DEGMAX; }
    if (n0 > NCAP_MAX - 200) { printf("0 0\n"); return 0; }

    xa = (int *)calloc((size_t)m0 + 1, sizeof(int));
    xb = (int *)calloc((size_t)m0 + 1, sizeof(int));
    if (!xa || !xb) { printf("0 0\n"); return 0; }
    if (empty_in) {
        k = 0;
        for (i = 0; i < DEGMAX; i++)
            for (v = 0; v < DEGMAX; v++) { xa[k] = i; xb[k] = DEGMAX + v; k++; }
    } else {
        for (i = 0; i < m0; i++)
            if (scanf("%d %d", &xa[i], &xb[i]) != 2) { printf("0 0\n"); return 0; }
    }

    NCAP = n0 + 400;
    if (NCAP > NCAP_MAX) NCAP = NCAP_MAX;
    WCAP = (NCAP + 63) / 64;
    side_ = (int *)calloc(NCAP, sizeof(int));
    deg_ = (int *)calloc(NCAP, sizeof(int));
    tdeg = (int *)calloc(NCAP, sizeof(int));
    col = (int *)calloc(NCAP, sizeof(int));
    d0_ = (int *)calloc(NCAP, sizeof(int));
    d1_ = (int *)calloc(NCAP, sizeof(int));
    nbr_ = (int *)calloc((size_t)NCAP * DEGMAX + 1, sizeof(int));
    ea_ = (int *)calloc((size_t)NCAP * DEGMAX + 1, sizeof(int));
    eb_ = (int *)calloc((size_t)NCAP * DEGMAX + 1, sizeof(int));
    best_ea_ = (int *)calloc((size_t)NCAP * DEGMAX + 1, sizeof(int));
    best_eb_ = (int *)calloc((size_t)NCAP * DEGMAX + 1, sizeof(int));
    adjm_ = (unsigned char *)calloc((size_t)NCAP * NCAP, 1);
    bufA_ = (uint64_t *)calloc((size_t)NCAP * WCAP, sizeof(uint64_t));
    bufB_ = (uint64_t *)calloc((size_t)NCAP * WCAP, sizeof(uint64_t));
    if (!side_ || !deg_ || !tdeg || !col || !d0_ || !d1_ || !nbr_ || !ea_ || !eb_ ||
        !best_ea_ || !best_eb_ || !adjm_ || !bufA_ || !bufB_) { printf("0 0\n"); return 0; }

    /* Validate input: range, no loops, no duplicates, degree <= DEGMAX. */
    for (i = 0; i < m0 && !bad; i++) {
        int u = xa[i], w = xb[i];
        if (u < 0 || w < 0 || u >= n0 || w >= n0 || u == w || ADJ(u, w)) { bad = 1; break; }
        ADJ(u, w) = 1; ADJ(w, u) = 1;
        if (++tdeg[u] > DEGMAX || ++tdeg[w] > DEGMAX) { bad = 1; break; }
    }
    for (i = 0; i < m0; i++) {
        int u = xa[i], w = xb[i];
        if (u >= 0 && u < n0 && w >= 0 && w < n0) { ADJ(u, w) = 0; ADJ(w, u) = 0; }
    }
    if (bad) { printf("0 0\n"); return 0; }

    /* Bipartition by propagation. */
    for (v = 0; v < n0; v++) col[v] = -1;
    for (;;) {
        int changed = 0;
        for (i = 0; i < m0; i++) {
            int u = xa[i], w = xb[i];
            if (col[u] >= 0 && col[w] < 0) { col[w] = 1 - col[u]; changed = 1; }
            else if (col[w] >= 0 && col[u] < 0) { col[u] = 1 - col[w]; changed = 1; }
        }
        if (changed) continue;
        found = -1;
        for (v = 0; v < n0; v++) if (col[v] < 0) { found = v; break; }
        if (found < 0) break;
        col[found] = 0;
    }
    for (i = 0; i < m0; i++) if (col[xa[i]] == col[xb[i]]) { printf("0 0\n"); return 0; }
    for (v = 0; v < n0; v++) side_[v] = col[v];

    N = 0; EM = 0;
    load_edges(n0, m0, xa, xb);
    cur = evalcost();
    if (cur == 0) save_best();

    while (elapsed() < tlim_) {
        if (cur == 0) {
            save_best();
            if (N >= NCAP - 1) break;
            side_[N] = rnd_int(2);
            deg_[N] = 0;
            N++;
            cur = evalcost();
            moves = 0;
            continue;
        }
        if (moves >= MAXMOVES) {
            if (have_best) load_edges(best_N, best_M, best_ea_, best_eb_);
            else load_edges(n0, m0, xa, xb);
            cur = evalcost();
            moves = 0;
            continue;
        }
        moves++;
        {
            double T = Tmax * pow(Tmin / Tmax, (double)moves / (double)MAXMOVES);
            long long c2;
            double delta;
            int ok;
            logging_ = 1; nlog_ = 0;
            ok = propose();
            logging_ = 0;
            if (!ok) { nlog_ = 0; continue; }
            c2 = evalcost();
            delta = (double)(c2 - cur);
            if (delta <= 0 || rnd_d() < exp(-delta / T)) cur = c2;
            else undo();
            nlog_ = 0;
        }
    }

    if (!have_best) { printf("0 0\n"); return 0; }
    printf("%d %d\n", best_N, best_M);
    for (i = 0; i < best_M; i++) printf("%d %d\n", best_ea_[i], best_eb_[i]);
    return 0;
}
'''


def _c_refine(d, D, seed, start, budget, timeout):
    """Run the C vertex-extension annealer from start; return parsed (n, edges)."""
    out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}"],
                    stdin_graph=start, timeout=timeout)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t_start = time.monotonic()

    def used():
        return time.monotonic() - t_start

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Arc-extended projective plane graphs (diameter 3, valid for D >= 3).
    if D >= 3:
        cands = _arc_extensions(d, t_start + 0.25 * time_limit,
                                random.Random(seed * 7919 + d))
        cands.sort(key=lambda t: -t[0])
        for n_c, e_c in cands:
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and used() < 0.25 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Python voltage-lift annealing, kept for larger diameters.
    if D >= 4:
        py_deadline = t_start + 0.3 * time_limit
        rng = random.Random(seed)
        ks = [1, 2, 2, 3, 4] if D >= 5 else [1, 1, 2, 3]
        while time.monotonic() < py_deadline:
            k = rng.choice(ks)
            base = best_n // (2 * k)
            G = max(2, base + 1 + rng.randrange(0, max(3, base // 8 + 1)))
            g = _sample_group(G, rng)
            if g is None:
                continue
            order, mul = g
            res = _anneal(d, D, k, order, mul, rng, py_deadline, iters=400)
            if res is not None:
                consider(res[0], res[1])

    # C refinement: try to add vertices to the best valid graph found so far.
    if D >= 2 and best_n < lib.moore_bound(d, D):
        left = 0.9 * time_limit - used() - 2.0
        if left > 2.0:
            budget = max(0.5, left * 0.9)
            try:
                n2, e2 = _c_refine(d, D, seed, best, budget, left)
                consider(n2, e2)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
