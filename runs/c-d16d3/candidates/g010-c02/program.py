import math
import random
import time
import itertools

import lib


# ----------------------------------------------------------------------------
# NEW ENGINE (C): Haar-type bi-Cayley graphs over small groups for diameter 3.
#
# Take a group G of order g and a set S of d elements. Join A_x to B_{x*s}
# for all x in G and s in S. The graph is bipartite, d-regular, and has 2g
# vertices. If S*S^{-1} = G and S^{-1}*S = G, every pair of vertices is within
# distance 3, so the graph is valid for D = 3. Since |S*S^{-1}| <= d(d-1)+1,
# this family reaches up to 2(d(d-1)+1) vertices.
#
# The C engine groups G as Z_m x| Z_k (r^k = 1 mod m) and runs simulated
# annealing over S, minimising the number of uncovered elements of S*S^{-1}
# and S^{-1}*S, with incremental count updates.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXG 1000
#define MAXD 64

static int G, M, K, dd;
static int pw[MAXG];
static int mt[MAXG * MAXG];
static int itv[MAXG];
static int S[MAXD];
static int inS[MAXG];
static int c1[MAXG], c2[MAXG];
static int uncov;
static uint64_t rs;
static clock_t T0C;
static double BUDGET;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndint(int n) { return (int)(rnd() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0C) / CLOCKS_PER_SEC; }

static int gcd_i(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_m x|_r Z_k, element a*k+b, (a,b)(c,d) = (a + r^b c, b+d). */
static void build_group(int g, int m, int k, int r) {
    G = g; M = m; K = k;
    for (int b = 0; b < k; b++) pw[b] = (m == 1) ? 0 : powmod(r, b, m);
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        for (int y = 0; y < G; y++) {
            int c = y / k, d = y % k;
            int na = (int)(((long long)a + (long long)pw[b] * c) % m);
            int nb = (b + d) % k;
            mt[x * G + y] = na * k + nb;
        }
    }
    for (int x = 0; x < G; x++) {
        int a = x / k, b = x % k;
        int nb = (k - b) % k;
        int na = (int)((m - ((long long)pw[nb] * a) % m) % m);
        itv[x] = na * k + nb;
    }
}

static void sample_group(int g, int *om, int *ok, int *or_) {
    int divs[64], nd = 0;
    for (int k = 1; k <= g; k++) if (g % k == 0) divs[nd++] = k;
    int k = divs[rndint(nd)];
    int m = g / k;
    if (m == 1) { *om = 1; *ok = k; *or_ = 0; return; }
    if (k == 1) { *om = m; *ok = 1; *or_ = 1; return; }
    for (int t = 0; t < 400; t++) {
        int r = 1 + rndint(m - 1);
        if (gcd_i(r, m) == 1 && powmod(r, k, m) == 1 % m) {
            *om = m; *ok = k; *or_ = r; return;
        }
    }
    *om = g; *ok = 1; *or_ = 1;
}

static inline void cinc(int *c, int g, int s) {
    if (s > 0) {
        if (c[g] == 0) uncov--;
        c[g]++;
    } else {
        c[g]--;
        if (c[g] == 0) uncov++;
    }
}

/* Add (s=+1) or remove (s=-1) all ordered-pair contributions of element x with S[j], j != skip. */
static void touch(int x, int skip, int s) {
    for (int j = 0; j < dd; j++) {
        if (j == skip) continue;
        int y = S[j];
        cinc(c1, mt[x * G + itv[y]], s);   /* x y^-1 */
        cinc(c2, mt[itv[y] * G + x], s);   /* y^-1 x */
        cinc(c1, mt[y * G + itv[x]], s);   /* y x^-1 */
        cinc(c2, mt[itv[x] * G + y], s);   /* x^-1 y */
    }
}

static int anneal(long iters, double T0v, double T1v) {
    memset(inS, 0, sizeof(int) * G);
    for (int i = 0; i < dd;) {
        int x = rndint(G);
        if (!inS[x]) { inS[x] = 1; S[i++] = x; }
    }
    for (int g = 0; g < G; g++) { c1[g] = 0; c2[g] = 0; }
    c1[0] = 1; c2[0] = 1;
    for (int i = 0; i < dd; i++) {
        for (int j = 0; j < dd; j++) {
            if (j == i) continue;
            c1[mt[S[i] * G + itv[S[j]]]]++;
            c2[mt[itv[S[j]] * G + S[i]]]++;
        }
    }
    uncov = 0;
    for (int g = 1; g < G; g++) {
        if (!c1[g]) uncov++;
        if (!c2[g]) uncov++;
    }
    if (uncov == 0) return 1;
    for (long t = 0; t < iters; t++) {
        if (uncov == 0) return 1;
        if ((t & 1023) == 0 && elapsed() > BUDGET) return 0;
        int i = rndint(dd);
        int x = rndint(G);
        if (inS[x]) continue;
        int old = S[i];
        int before = uncov;
        touch(old, i, -1);
        S[i] = x;
        touch(x, i, 1);
        int delta = uncov - before;
        double T = T0v * pow(T1v / T0v, (double)t / (double)iters);
        if (delta <= 0 || rnd01() < exp(-delta / T)) {
            inS[old] = 0;
            inS[x] = 1;
        } else {
            touch(x, i, -1);
            S[i] = old;
            touch(old, i, 1);
        }
    }
    return uncov == 0;
}

int main(int argc, char **argv) {
    T0C = clock();
    if (argc < 5) { printf("0 0\n"); return 0; }
    int d = atoi(argv[1]);
    int D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], 0, 10);
    BUDGET = atof(argv[4]);
    int gmin = argc > 5 ? atoi(argv[5]) : 2;
    rs = seed * 2654435761ULL + 88172645463325252ULL;
    if (!rs) rs = 1;
    dd = d;
    if (D != 3 || d < 2 || d > MAXD) { printf("0 0\n"); return 0; }

    int Ghi = d * (d - 1) + 1;
    if (Ghi > MAXG - 1) Ghi = MAXG - 1;
    int Gb = gmin - 1;
    if (Gb < dd - 1) Gb = dd - 1;

    int found = 0, bG = 0, bM = 0, bK = 0, bR = 0;
    int bS[MAXD];
    long iters = 200000;

    while (elapsed() < BUDGET && Gb < Ghi) {
        int lo = Gb + 1;
        int hi = lo + (Ghi - lo) / 2;
        int target = lo + rndint(hi - lo + 1);
        int m, k, r;
        sample_group(target, &m, &k, &r);
        build_group(target, m, k, r);
        if (anneal(iters, 2.0, 0.05)) {
            Gb = target;
            found = 1;
            bG = target; bM = m; bK = k; bR = r;
            memcpy(bS, S, sizeof(int) * dd);
        }
    }

    if (!found) { printf("0 0\n"); return 0; }
    build_group(bG, bM, bK, bR);
    int n = 2 * bG;
    int me = dd * bG;
    printf("%d %d\n", n, me);
    for (int x = 0; x < bG; x++)
        for (int j = 0; j < dd; j++)
            printf("%d %d\n", x, bG + mt[x * bG + bS[j]]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Projective-plane based fallbacks (diameter 3).
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


def _side_colors(n, adj):
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
    return color


def _ball_masks(n, adj, R):
    """Bitmask of all vertices within distance R of each vertex."""
    reach = [1 << v for v in range(n)]
    for _ in range(R):
        new = [0] * n
        for v in range(n):
            r = reach[v]
            for u in adj[v]:
                r |= reach[u]
            new[v] = r
        reach = new
    return reach


def _augment(n, edges, d, D, rng, deadline, max_fails=60):
    """Greedily insert vertices whose neighbourhoods cover the graph within D. Returns (n, edges)."""
    if n == 0 or D < 2:
        return n, list(edges)
    adj = [set() for _ in range(n)]
    for u, v in edges:
        adj[u].add(v)
        adj[v].add(u)
    color = _side_colors(n, adj)
    R = D - 1
    fails = 0
    while time.monotonic() < deadline and fails < max_fails:
        balls = _ball_masks(n, adj, R)
        full = (1 << n) - 1
        added = False
        sides = [0, 1]
        rng.shuffle(sides)
        for side in sides:
            base_cand = [u for u in range(n) if color[u] == 1 - side and len(adj[u]) < d]
            if not base_cand:
                continue
            for _attempt in range(4):
                cand = base_cand[:]
                rng.shuffle(cand)
                covered = 0
                chosen = []
                pool = cand
                while covered != full and len(chosen) < d and pool:
                    best_gain, bu, bi = 0, None, -1
                    for i, u in enumerate(pool):
                        g = (balls[u] & ~covered).bit_count()
                        if g > best_gain:
                            best_gain, bu, bi = g, u, i
                    if bu is None:
                        break
                    chosen.append(bu)
                    covered |= balls[bu]
                    pool = pool[:bi] + pool[bi + 1:]
                if covered == full:
                    w = n
                    n += 1
                    adj.append(set())
                    color.append(side)
                    for u in chosen:
                        adj[u].add(w)
                        adj[w].add(u)
                    added = True
                    break
            if added:
                break
        if added:
            fails = 0
            continue
        fails += 1
        spare_a = [u for u in range(n) if len(adj[u]) < d and color[u] == 0]
        spare_b = [u for u in range(n) if len(adj[u]) < d and color[u] == 1]
        if spare_a and spare_b:
            for _ in range(20):
                u = rng.choice(spare_a)
                v = rng.choice(spare_b)
                if u != v and v not in adj[u]:
                    adj[u].add(v)
                    adj[v].add(u)
                    break
    out = [(u, v) for u in range(n) for v in adj[u] if u < v]
    return n, out


def _pg_fallback(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d (diameter 3)."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Glue.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D == 3 and d >= 3:
        pg = _pg_fallback(d)
        if pg is not None:
            consider(pg[0], pg[1])

        # Arc-extended PG graphs and greedy augmentation (kept as strong fallbacks).
        arcs = _arc_extensions(d, t0 + 0.12 * time_limit, random.Random(seed * 7919 + d))
        arcs.sort(key=lambda t: -t[0])
        for n_c, e_c in arcs[:3]:
            consider(n_c, e_c)
        if arcs:
            n_a, e_a = arcs[0]
            n2, e2 = _augment(n_a, e_a, d, D, rng, t0 + 0.25 * time_limit)
            consider(n2, e2)

        # Main search: bi-Cayley diameter-3 graphs over groups of order near d(d-1)+1.
        elapsed = time.monotonic() - t0
        budget = max(1.0, 0.8 * time_limit - elapsed - 1.5)
        timeout = min(0.92 * time_limit, budget + 6.0)
        gmin = best[0] // 2 + 1
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.2f}", gmin], timeout=timeout)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Other D (not the focus here): K_{d,d} fallback above is already valid.
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
