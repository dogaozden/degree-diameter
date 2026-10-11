import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New D = 3 engine: simulated annealing over bi-Cayley lifts.
#
# The graph is a lift over G = Z_m x| Z_k2 with k base vertices on each side.
# Layer L is a permutation p_L of {0..k-1}, and each dart (i, p_L(i), s) joins
# A_i x g to B_{p_L(i)} x (g*s). Each vertex gets exactly d edges, and the
# graph is bipartite by construction. Left multiplication by a group element
# is an automorphism, so distances only need checking from the 2k vertices
# A_i x e and B_j x e. The cost is the number of (rep, vertex) pairs at distance
# > D. The engine stops as soon as the cost is zero and prints the lift.
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1024
#define MAXG 512
#define MAXK 8
#define MAXD 64
#define MAXDART (MAXK * MAXD)
#define CYC 40000

static int d, D, k, G, N, ND;
static int gm, gk2, gr;
static int dj[MAXDART];
static int ds[MAXDART];
static int powr[MAXG];
static int mulT[MAXG * MAXG];
static int adj[MAXN][MAXD];
static int cntv[MAXN];
static int stamp[MAXN];
static int curstamp = 0;
static int qbuf[MAXN];
static uint64_t rs = 1;

static uint64_t rnd(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gmul(int x, int y) {
    int a = x / gk2, b = x % gk2, c = y / gk2, e = y % gk2;
    long A = ((long)a + (long)powr[b] * c) % gm;
    int Bv = (b + e) % gk2;
    return (int)(A * gk2 + Bv);
}

static void build_adj(void) {
    for (int v = 0; v < N; v++) cntv[v] = 0;
    for (int idx = 0; idx < ND; idx++) {
        int i = idx % k, j = dj[idx], s = ds[idx];
        for (int g = 0; g < G; g++) {
            int a = i * G + g;
            int b = k * G + j * G + mulT[g * G + s];
            adj[a][cntv[a]++] = b;
            adj[b][cntv[b]++] = a;
        }
    }
}

/* True if some other dart with the same A-index i has target j and shift s. */
static int conflict(int i, int j, int s, int excl) {
    for (int L = 0; L < d; L++) {
        int idx = L * k + i;
        if (idx != excl && dj[idx] == j && ds[idx] == s) return 1;
    }
    return 0;
}

static int dup_any(void) {
    for (int idx = 0; idx < ND; idx++)
        if (conflict(idx % k, dj[idx], ds[idx], idx)) return 1;
    return 0;
}

static long eval_cost(void) {
    build_adj();
    long total = 0;
    for (int rep = 0; rep < 2 * k; rep++) {
        int src = (rep < k) ? rep * G : k * G + (rep - k) * G;
        curstamp++;
        stamp[src] = curstamp;
        int qh = 0, qt = 0;
        qbuf[qt++] = src;
        for (int lev = 0; lev < D && qh < qt; lev++) {
            int lend = qt;
            while (qh < lend) {
                int u = qbuf[qh++];
                for (int t = 0; t < d; t++) {
                    int v = adj[u][t];
                    if (stamp[v] != curstamp) { stamp[v] = curstamp; qbuf[qt++] = v; }
                }
            }
        }
        total += N - qt;
    }
    return total;
}

static void emit(void) {
    printf("%d %d\n", N, ND * G);
    for (int idx = 0; idx < ND; idx++) {
        int i = idx % k, j = dj[idx], s = ds[idx];
        for (int g = 0; g < G; g++)
            printf("%d %d\n", i * G + g, k * G + j * G + mulT[g * G + s]);
    }
}

int main(int argc, char **argv) {
    if (argc < 9) return 1;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs = 0x9E3779B97F4A7C15ULL ^ ((uint64_t)strtoull(argv[3], NULL, 10) * 0xBF58476D1CE4E5B9ULL + 977ULL);
    if (rs == 0) rs = 1;
    double tl = atof(argv[4]);
    k = atoi(argv[5]);
    gm = atoi(argv[6]);
    gk2 = atoi(argv[7]);
    gr = atoi(argv[8]);
    if (d < 1 || d > MAXD || D < 1 || k < 1 || k > MAXK || gm < 1 || gk2 < 1) {
        printf("0 0\n");
        return 0;
    }
    G = gm * gk2;
    if (G > MAXG || 2 * k * G > MAXN) {
        printf("0 0\n");
        return 0;
    }
    N = 2 * k * G;
    ND = d * k;
    gr %= gm;
    powr[0] = 1 % gm;
    for (int b = 1; b < gk2; b++) powr[b] = (int)(((long)powr[b - 1] * gr) % gm);
    for (int x = 0; x < G; x++)
        for (int y = 0; y < G; y++)
            mulT[x * G + y] = gmul(x, y);

    /* Random initial layers: each layer is a permutation of the k A-indices. */
    int perm[MAXK];
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < k; i++) perm[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < k; i++) {
            dj[L * k + i] = perm[i];
            ds[L * k + i] = rint_(G);
        }
    }
    for (int pass = 0; pass < 100000; pass++) {
        int bad = 0;
        for (int idx = 0; idx < ND; idx++) {
            if (conflict(idx % k, dj[idx], ds[idx], idx)) {
                ds[idx] = rint_(G);
                bad = 1;
            }
        }
        if (!bad) break;
    }
    if (dup_any()) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    long cur = eval_cost();
    if (cur == 0) {
        emit();
        return 0;
    }

    long it = 0;
    for (;;) {
        if ((it & 63) == 0) {
            double el = (double)(clock() - t0) / CLOCKS_PER_SEC;
            if (el > tl) break;
        }
        it++;
        double phase = (double)(it % CYC) / (double)CYC;
        double T = 0.3 + 4.0 * (1.0 - phase) * (1.0 - phase);

        if (k >= 2 && rint_(100) < 40) {
            /* swap the targets of two A-indices inside one layer */
            int L = rint_(d);
            int i1 = rint_(k), i2 = rint_(k - 1);
            if (i2 >= i1) i2++;
            int a = L * k + i1, b = L * k + i2;
            if (conflict(i1, dj[b], ds[a], a) || conflict(i2, dj[a], ds[b], b)) continue;
            int t = dj[a]; dj[a] = dj[b]; dj[b] = t;
            long c2 = eval_cost();
            long delta = c2 - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                t = dj[a]; dj[a] = dj[b]; dj[b] = t;
            }
        } else {
            /* change one shift */
            int idx = rint_(ND);
            int old = ds[idx];
            int ns = rint_(G);
            if (ns == old || conflict(idx % k, dj[idx], ns, idx)) continue;
            ds[idx] = ns;
            long c2 = eval_cost();
            long delta = c2 - cur;
            if (delta <= 0 || rdbl() < exp(-(double)delta / T)) {
                cur = c2;
            } else {
                ds[idx] = old;
            }
        }
        if (cur == 0) {
            emit();
            return 0;
        }
    }
    printf("0 0\n");
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
# Lift candidates for the D = 3 annealer.
# ----------------------------------------------------------------------------

def _lift_candidates(lo, hi, rng):
    """Return (N, k, m, k2, r) tuples with N = 2*k*(m*k2) in [lo, hi]. Cyclic has k2 = 1, r = 1."""
    out = []
    for k in range(1, 7):
        for N in range(lo, hi + 1):
            if N % (2 * k):
                continue
            G = N // (2 * k)
            out.append((N, k, G, 1, 1))
            for k2 in (2, 3, 4, 5, 6, 8):
                if G % k2:
                    continue
                m = G // k2
                if m < 2:
                    continue
                rr = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1]
                rng.shuffle(rr)
                for r in rr[:2]:
                    out.append((N, k, m, k2, r))
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
# Build
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t_start = time.monotonic()
    end = t_start + 0.85 * time_limit - 2.0
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

    # D = 3: annealing over group lifts with 2k base vertices, aiming above the
    # current best. Each run is a short time slice; the best valid result is kept.
    if D == 3:
        bound = lib.moore_bound(d, D)
        if best[0] < bound:
            lo = best[0] + 2
            hi = min(bound, best[0] + 60)
            pool = _lift_candidates(lo, hi, rng)
            rng.shuffle(pool)
            tries = 0
            while time.monotonic() < end - 1.5:
                pool = [c for c in pool if best[0] < c[0] <= bound]
                if not pool:
                    break
                cand = pool[tries % len(pool)]
                tries += 1
                secs = min(6.0, end - time.monotonic() - 0.5)
                if secs < 1.0:
                    break
                try:
                    out = lib.run_c(LIFT_C, [d, D, seed * 1000 + tries, round(secs, 2), *cand[1:]],
                                    timeout=secs + 6)
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
