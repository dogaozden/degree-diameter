import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley / voltage-lift search for D = 3 (any D >= 3 works).
#
# A lift has K base vertices per side and a group G = Z_M x|_r Z_K2 (order
# G = M*K2). Each side-layer has G vertices. For every L in 0..d-1 the darts
# form a permutation p_L of the K layers, and dart (i, p_L[i], s) joins
# A_{i,g} to B_{p_L[i], g*s}. Every vertex then has degree exactly d and the
# graph is bipartite by construction. Left multiplication by the group is an
# automorphism, so BFS from one A and one B representative per layer checks
# the full diameter. Simulated annealing moves the connection elements s and
# the target permutations, minimising the number of unreached (rep, vertex)
# pairs. The engine returns the largest valid lift with order >= nmin found
# within the time limit, or "0 0".
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1300
#define MAXV 2600
#define DCAP 24
#define MAXT 80
#define BIGC 1000000000L

static int d, D, K, G, K2, M, N;
static uint64_t rs = 1;
static int powr[64];
static int dI[MAXT], dJ[MAXT], dS[MAXT], nd;
static int pm[MAXT][MAXG];
static int adj[MAXV][DCAP], deg[MAXV];
static int seen[MAXV], stampc = 0;
static int fr[MAXV], nx[MAXV];
static int bestU[MAXV * DCAP], bestV[MAXV * DCAP];
static int bestN = 0, bestM = 0;
static clock_t T0;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rnd_int(int k) { return (int)(rnd64() % (uint64_t)k); }
static double rnd_dbl(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }
static long powmod_l(long b, long e, long m) {
    long r = 1 % m; b %= m;
    while (e) { if (e & 1) r = r * b % m; b = b * b % m; e >>= 1; }
    return r;
}

/* Semidirect product Z_M x| Z_K2 with (a,b)(c,e) = (a + r^b c, b + e). Element (a,b) = a*K2 + b. */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    int na = (int)(((long)a + (long)powr[b] * c) % M);
    int nb = (b + e) % K2;
    return na * K2 + nb;
}

static void set_row(int t) {
    for (int g = 0; g < G; g++) pm[t][g] = gmul(g, dS[t]);
}

static int try_config(int Kc, int Gc) {
    K = Kc; G = Gc; N = 2 * K * G;
    if (K < 1 || G < 2 || N > MAXV || G > MAXG) return 0;
    int divs[64], nn = 0;
    for (int f = 1; f <= 12 && f <= G; f++)
        if (G % f == 0 && G / f >= 2) divs[nn++] = f;
    if (nn == 0) return 0;
    K2 = divs[rnd_int(nn)];
    M = G / K2;
    int r = 1 % M;
    if (K2 > 1 && M >= 3) {
        for (int t = 0; t < 300; t++) {
            int c = 2 + rnd_int(M - 2);
            if (gcd_i(c, M) == 1 && powmod_l(c, K2, M) == 1 % M) { r = c; break; }
        }
    }
    powr[0] = 1 % M;
    for (int b = 1; b < K2; b++) powr[b] = (int)((long)powr[b - 1] * r % M);
    return 1;
}

static void random_darts(void) {
    nd = 0;
    for (int L = 0; L < d; L++) {
        int p[4];
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rnd_int(i + 1);
            int tmp = p[i]; p[i] = p[j]; p[j] = tmp;
        }
        for (int i = 0; i < K; i++) {
            dI[nd] = i; dJ[nd] = p[i]; dS[nd] = rnd_int(G);
            nd++;
        }
    }
    for (int t = 0; t < nd; t++) set_row(t);
}

static int has_dup(void) {
    for (int t1 = 0; t1 < nd; t1++)
        for (int t2 = t1 + 1; t2 < nd; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) return 1;
    return 0;
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) deg[v] = 0;
    for (int t = 0; t < nd; t++) {
        int ba = dI[t] * G, bb = (K + dJ[t]) * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[t][g];
            adj[a][deg[a]++] = b;
            adj[b][deg[b]++] = a;
        }
    }
}

/* Total number of (representative, vertex) pairs not reached within distance D. */
static long cost_fn(void) {
    if (has_dup()) return BIGC;
    build_adj();
    long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = r * G;
        stampc++;
        int fc = 0;
        fr[fc++] = src; seen[src] = stampc;
        int count = 1;
        for (int lv = 0; lv < D && fc > 0; lv++) {
            int nc = 0;
            for (int a = 0; a < fc; a++) {
                int u = fr[a];
                for (int e = 0; e < deg[u]; e++) {
                    int v = adj[u][e];
                    if (seen[v] != stampc) { seen[v] = stampc; nx[nc++] = v; }
                }
            }
            count += nc;
            for (int a = 0; a < nc; a++) fr[a] = nx[a];
            fc = nc;
        }
        total += N - count;
    }
    return total;
}

static void save_graph(void) {
    int m = 0;
    for (int t = 0; t < nd; t++) {
        for (int g = 0; g < G; g++) {
            bestU[m] = dI[t] * G + g;
            bestV[m] = (K + dJ[t]) * G + pm[t][g];
            m++;
        }
    }
    bestM = m;
    bestN = N;
}

static int accept(long c2, long cur, double T) {
    if (c2 <= cur) return 1;
    return rnd_dbl() < exp(-(double)(c2 - cur) / T);
}

int main(int argc, char **argv) {
    if (argc < 7) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    uint64_t seed = (uint64_t)strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    int nmin = atoi(argv[5]);
    int kmax = atoi(argv[6]);
    rs = 0x9E3779B97F4A7C15ULL ^ (seed * 0xBF58476D1CE4E5B9ULL + 777ULL);
    if (rs == 0) rs = 1;
    T0 = clock();
    if (d < 1 || d > 20 || D < 3 || kmax < 1 || kmax > 3 || nmin < 1) {
        printf("0 0\n");
        return 0;
    }
    bestN = nmin - 1;
    bestM = 0;

    while (elapsed() < tl) {
        int Kc = 1 + rnd_int(kmax);
        int minG = (bestN + 2 * Kc) / (2 * Kc);   /* ceil((bestN+1)/(2K)) */
        if (minG < 2) minG = 2;
        int Gc = minG + rnd_int(4);
        if (!try_config(Kc, Gc)) continue;

        random_darts();
        long cur = cost_fn();
        const int maxit = 30000;
        for (int it = 0; it < maxit && cur > 0; it++) {
            if ((it & 127) == 0 && elapsed() > tl) break;
            double frac = (double)it / maxit;
            double T = 0.3 + 2.0 * (1.0 - frac);
            if (K >= 2 && rnd_int(10) >= 7) {
                int L = rnd_int(d);
                int a = rnd_int(K), b = rnd_int(K);
                if (a == b) continue;
                int ta = L * K + a, tb = L * K + b;
                int tmp = dJ[ta]; dJ[ta] = dJ[tb]; dJ[tb] = tmp;
                long c2 = cost_fn();
                if (accept(c2, cur, T)) cur = c2;
                else { tmp = dJ[ta]; dJ[ta] = dJ[tb]; dJ[tb] = tmp; }
            } else {
                int t = rnd_int(nd);
                int old = dS[t];
                int nw = rnd_int(G);
                if (nw == old) continue;
                dS[t] = nw; set_row(t);
                long c2 = cost_fn();
                if (accept(c2, cur, T)) cur = c2;
                else { dS[t] = old; set_row(t); }
            }
        }
        if (cur == 0 && N > bestN) save_graph();
    }

    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int i = 0; i < bestM; i++) printf("%d %d\n", bestU[i], bestV[i]);
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
    """Conic (plus nucleus for even q) as a point-index set."""
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
# Python voltage-lift annealing for D >= 4 (unchanged from parent).
# ----------------------------------------------------------------------------

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


_BIG = 10 ** 9


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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.88 * time_limit - 1.0
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

    # Arc-extended projective plane graphs (valid for D >= 3). Safe base.
    if D >= 3 and time.monotonic() < end:
        cands = _arc_extensions(d, end, random.Random(seed * 7919 + d))
        for g in sorted(cands, key=lambda t: -t[0]):
            consider(g)

    # Generalized quadrangle (valid for D >= 4).
    if D >= 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)

    # Bold change for D = 3: search bi-Cayley / voltage lifts of a different
    # kind (semidirect groups, K in 1..3 base layers) in C, asking for order
    # above the current best. Falls back to the arc graph if nothing is found.
    if D == 3 and d <= 20 and best[0] < lib.moore_bound(d, D):
        budget = end - time.monotonic() - 1.0
        if budget > 3.0:
            try:
                out = lib.run_c(C_LIFT, [d, D, seed, round(budget - 0.5, 2), best[0] + 1, 3],
                                timeout=budget + 5)
                consider(lib.parse_graph_text(out))
            except Exception:
                pass

    # Voltage-lift annealing for D >= 4 (unchanged from parent).
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
