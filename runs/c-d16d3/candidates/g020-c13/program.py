import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: simulated annealing over bi-Cayley voltage lifts of a semidirect
# product group Z_M x| Z_KS (element (a,b) coded as a*KS+b), with K base layers
# per side and d darts per layer. Cost = number of (representative, vertex)
# pairs not reached within distance D; cost 0 gives a valid graph.
# Left multiplication is an automorphism, so representatives are one per layer.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>
#include <stdint.h>
#include <math.h>

#define MAXD 40
#define MAXK 16
#define MAXG 1000
#define BIG 1000000000L

static int d, D, K, G, M, KS, R;
static int *mulT;
static int dj[MAXD][MAXK];
static int ds[MAXD][MAXK];
static int *adj, *deg, *seen, *dep, *queue;
static int stamp = 0;
static int NV;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0g;
static double tl;

static uint64_t rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rndi(int n) { return (int)(rnd() % (uint64_t)n); }
static double rndu(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0g) / CLOCKS_PER_SEC; }

static void randomize(void) {
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < K; i++) dj[L][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndi(i + 1);
            int t = dj[L][i]; dj[L][i] = dj[L][j]; dj[L][j] = t;
        }
        for (int i = 0; i < K; i++) ds[L][i] = rndi(G);
    }
}

static long cost_eval(void) {
    for (int L = 0; L < d; L++)
        for (int L2 = 0; L2 < L; L2++)
            for (int i = 0; i < K; i++)
                if (dj[L][i] == dj[L2][i] && ds[L][i] == ds[L2][i]) return BIG;
    memset(deg, 0, sizeof(int) * NV);
    for (int L = 0; L < d; L++) {
        for (int i = 0; i < K; i++) {
            int j = dj[L][i], s = ds[L][i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + j) * G + mulT[g * G + s];
                adj[a * d + deg[a]++] = b;
                adj[b * d + deg[b]++] = a;
            }
        }
    }
    long total = 0;
    for (int r = 0; r < 2 * K; r++) {
        int src = (r < K) ? r * G : (K + (r - K)) * G;
        stamp++;
        int head = 0, tail = 0;
        queue[tail++] = src; seen[src] = stamp; dep[src] = 0;
        while (head < tail) {
            int u = queue[head++];
            if (dep[u] >= D) continue;
            for (int k = 0; k < d; k++) {
                int v = adj[u * d + k];
                if (seen[v] != stamp) {
                    seen[v] = stamp; dep[v] = dep[u] + 1;
                    queue[tail++] = v;
                }
            }
        }
        total += NV - tail;
    }
    return total;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 0; }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    rs ^= (uint64_t)atoll(argv[3]) * 2654435761ULL + 1;
    for (int w = 0; w < 5; w++) rnd();
    tl = atof(argv[4]);
    M = atoi(argv[5]);
    KS = atoi(argv[6]);
    R = atoi(argv[7]);
    K = atoi(argv[8]);
    G = M * KS;
    if (d < 1 || d > MAXD || K < 1 || K > MAXK || G < 2 || G > MAXG || M < 1 || KS < 1 || D < 1) {
        printf("0 0\n");
        return 0;
    }
    mulT = malloc(sizeof(int) * G * G);
    long long *pw = malloc(sizeof(long long) * KS);
    pw[0] = 1 % M;
    for (int b = 1; b < KS; b++) pw[b] = (pw[b - 1] * R) % M;
    for (int x = 0; x < G; x++) {
        int a = x / KS, b = x % KS;
        for (int y = 0; y < G; y++) {
            int c = y / KS, e = y % KS;
            long long aa = (a + pw[b] * c) % M;
            mulT[x * G + y] = (int)(aa * KS + (b + e) % KS);
        }
    }
    NV = 2 * K * G;
    adj = malloc(sizeof(int) * NV * d);
    deg = malloc(sizeof(int) * NV);
    seen = calloc(NV, sizeof(int));
    dep = malloc(sizeof(int) * NV);
    queue = malloc(sizeof(int) * NV);

    t0g = clock();
    int found = 0;
    while (!found && elapsed() < tl) {
        randomize();
        long c = cost_eval();
        const long ITERS = 400000;
        for (long it = 0; it < ITERS && c > 0; it++) {
            if ((it & 255) == 0 && elapsed() > tl) break;
            double T = 1.5 * pow(0.02 / 1.5, (double)it / (double)ITERS);
            if (K > 1 && rndu() < 0.4) {
                int L = rndi(d), a = rndi(K), b = rndi(K);
                if (a == b) continue;
                int t = dj[L][a]; dj[L][a] = dj[L][b]; dj[L][b] = t;
                long c2 = cost_eval();
                long delta = c2 - c;
                if (delta <= 0 || rndu() < exp(-(double)delta / T)) c = c2;
                else { t = dj[L][a]; dj[L][a] = dj[L][b]; dj[L][b] = t; }
            } else {
                int L = rndi(d), i = rndi(K);
                int old = ds[L][i];
                int nw = rndi(G);
                if (nw == old) continue;
                ds[L][i] = nw;
                long c2 = cost_eval();
                long delta = c2 - c;
                if (delta <= 0 || rndu() < exp(-(double)delta / T)) c = c2;
                else ds[L][i] = old;
            }
        }
        if (c == 0) found = 1;
    }
    if (!found) { printf("0 0\n"); return 0; }
    printf("%d %d\n", NV, d * K * G);
    for (int L = 0; L < d; L++)
        for (int i = 0; i < K; i++) {
            int j = dj[L][i], s = ds[L][i];
            for (int g = 0; g < G; g++)
                printf("%d %d\n", i * G + g, (K + j) * G + mulT[g * G + s]);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Arc-extended projective plane incidence graphs (diameter 3). Safe fallback.
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
# Generalized quadrangle W(q) baseline (D = 4).
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
# Group choice for the C lift search.
# ----------------------------------------------------------------------------

def _pick_group(G, rng):
    """Return (KS, M, R) with G = M*KS and Z_M x| Z_KS (R^KS = 1 mod M), or None."""
    divs = [k for k in range(1, G + 1) if G % k == 0 and G // k >= 2]
    if not divs:
        return None
    for _ in range(40):
        KS = rng.choice(divs)
        M = G // KS
        if KS == 1:
            return (1, M, 1)
        cands = [r for r in range(2, M) if math.gcd(r, M) == 1 and pow(r, KS, M) == 1 % M]
        if cands:
            return (KS, M, rng.choice(cands))
    return None


# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    deadline = t0 + 0.8 * time_limit
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    if D >= 3:
        for n_c, e_c in _arc_extensions(d, t0 + 0.25 * time_limit, random.Random(seed * 7919 + d)):
            if n_c > best_n:
                consider(n_c, e_c)

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search: C annealing over semidirect lifts with K base layers per side.
    call = 0
    while time.monotonic() < deadline - 1.0:
        K = rng.choice([1, 2, 2, 3, 4])
        target = best_n // (2 * K) + 1
        G = target + rng.randrange(0, max(2, target // 12))
        if G < max(2, d) or G > 1000:
            continue
        grp = _pick_group(G, rng)
        if grp is None:
            continue
        KS, M, R = grp
        budget = min(5.0, deadline - time.monotonic() - 0.5)
        if budget < 0.5:
            break
        call += 1
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed * 1000 + call, budget, M, KS, R, K],
                            timeout=budget + 10)
            n, e = lib.parse_graph_text(out)
        except Exception:
            continue
        if n > best_n:
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
