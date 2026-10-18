import itertools
import random
import time

import lib


# ----------------------------------------------------------------------------
# New search family: bi-Cayley graphs with ONE base vertex per side (Haar-type).
#
# Vertices: a_x (x in G) and b_y (y in G), G a finite group of order n/2.
# Edges:    a_x -- b_{x s} for s in S, |S| = d (distinct).
# Since left multiplication is an automorphism, the graph has diameter <= D
# iff every vertex of a_e and of b_e reaches everything within D steps. The
# annealer therefore runs just two BFS per move on a graph of 2|G| vertices.
#
# Groups: semidirect products Z_m x| Z_k (element (a,b) coded a*k+b, with
# (a,b)(c,e) = (a + r^b c, b + e), r^k = 1 mod m), including cyclic and
# non-abelian cases, so expansion is not limited by abelian growth.
#
# Search: for a goal order, sample a random group and connection set, then
# simulated annealing on the number of unreached pairs. On success, raise the
# goal order and continue. The best valid graph is kept.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXKK 64
#define NKC 13
#define ITERS 12000

static const int KCHOICE[NKC] = {1,1,1,2,2,2,3,4,5,6,8,10,12};

static uint64_t rs;
static uint64_t rnd64(void) {
    uint64_t x = rs;
    x ^= x >> 12;
    x ^= x << 25;
    x ^= x >> 27;
    rs = x;
    return x * 2685821657736338717ULL;
}
static double rnd01(void) {
    return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0);
}
static int rndint(int n) {
    return (int)(rnd64() % (uint64_t)n);
}

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + (double)ts.tv_nsec * 1e-9;
}

static int DEG, DIAM, CAPG;
static int G, KK, MM, RR;
static int PW[MAXKK];
static int *S, *Sinv, *mark, *nA, *nB, *bestA;
static int *stamp, *dist, *queue;
static int curstamp;
static int bestG, have_best;

static int64_t powmod64(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int64_t gcd64(int64_t a, int64_t b) {
    while (b) {
        int64_t t = a % b;
        a = b;
        b = t;
    }
    return a;
}

/* Choose r with gcd(r,m)=1 and r^k = 1 mod m. Falls back to r = 1 (direct product). */
static int sample_r(int mm, int kk) {
    if (kk == 1) return 1 % mm;
    if (kk > MAXKK) return 1 % mm;
    if (kk % 2 == 0 && rnd01() < 0.5) return mm - 1;
    for (int t = 0; t < 300; t++) {
        int c = 2 + rndint(mm - 2 > 0 ? mm - 2 : 1);
        if (c >= mm) continue;
        if (gcd64(c, mm) == 1 && powmod64(c, kk, mm) == 1 % mm) return c;
    }
    return 1 % mm;
}

static void set_group(int mm, int kk, int r) {
    MM = mm;
    KK = kk;
    RR = r;
    G = MM * KK;
    PW[0] = 1 % MM;
    for (int b = 1; b < KK; b++) PW[b] = (int)((int64_t)PW[b - 1] * RR % MM);
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static inline int gmul(int x, int y) {
    int a = x / KK, b = x % KK, c = y / KK, d = y % KK;
    int64_t a2 = ((int64_t)a + (int64_t)PW[b] * c) % MM;
    int b2 = (b + d) % KK;
    return (int)(a2 * KK + b2);
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static inline int ginv(int x) {
    int a = x / KK, b = x % KK;
    int nb = (KK - b) % KK;
    int64_t a2 = (MM - ((int64_t)PW[nb] * a) % MM) % MM;
    return (int)(a2 * KK + nb);
}

/* Set connection element i to s and refresh both neighbour columns. */
static void set_col(int i, int s) {
    S[i] = s;
    int si = ginv(s);
    Sinv[i] = si;
    for (int x = 0; x < G; x++) nA[x * DEG + i] = gmul(x, s);
    for (int y = 0; y < G; y++) nB[y * DEG + i] = gmul(y, si);
}

/* a_x has neighbours b_{x s}; b_y has neighbours a_{y s^{-1}}.
   Vertex ids: a_x = x, b_y = G + y. Returns the number of vertices not within DIAM of src. */
static int64_t bfs_unreached(int src) {
    curstamp++;
    int head = 0, tail = 0, reached = 1;
    stamp[src] = curstamp;
    dist[src] = 0;
    queue[tail++] = src;
    while (head < tail) {
        int v = queue[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        if (v < G) {
            const int *row = nA + (size_t)v * DEG;
            for (int i = 0; i < DEG; i++) {
                int w = G + row[i];
                if (stamp[w] != curstamp) {
                    stamp[w] = curstamp;
                    dist[w] = dv + 1;
                    queue[tail++] = w;
                    reached++;
                }
            }
        } else {
            const int *row = nB + (size_t)(v - G) * DEG;
            for (int i = 0; i < DEG; i++) {
                int w = row[i];
                if (stamp[w] != curstamp) {
                    stamp[w] = curstamp;
                    dist[w] = dv + 1;
                    queue[tail++] = w;
                    reached++;
                }
            }
        }
    }
    return (int64_t)(2 * G - reached);
}

/* Left multiplication is an automorphism, so a_e and b_e suffice. */
static int64_t eval_cost(void) {
    return bfs_unreached(0) + bfs_unreached(G);
}

static int anneal(int iters, double deadline, int64_t *final_cost) {
    int64_t cost = eval_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    double T0 = 0.05 * c0;
    if (T0 < 2.0) T0 = 2.0;
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 127) == 0 && now_s() > deadline) break;
        double frac = (double)t / iters;
        double T = T0 * pow(0.02, frac);
        int i = rndint(DEG);
        int nw = rndint(G);
        if (mark[nw]) continue;
        int old = S[i];
        set_col(i, nw);
        int64_t c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            mark[old] = 0;
            mark[nw] = 1;
            cost = c2;
        } else {
            set_col(i, old);
        }
    }
    *final_cost = cost;
    return cost == 0;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        fprintf(stderr, "usage: d D best cap seed time\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best0 = atoll(argv[3]);
    long long cap = atoll(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    double TL = atof(argv[6]);
    double t0 = now_s();

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DIAM < 3) {
        printf("0 0\n");
        return 0;
    }
    long long cg = cap / 2;
    if (cg < DEG + 1) {
        printf("0 0\n");
        return 0;
    }
    if (cg > 2000000) cg = 2000000;
    CAPG = (int)cg;

    S = malloc(sizeof(int) * (size_t)DEG);
    Sinv = malloc(sizeof(int) * (size_t)DEG);
    mark = calloc((size_t)CAPG, sizeof(int));
    nA = malloc(sizeof(int) * (size_t)CAPG * DEG);
    nB = malloc(sizeof(int) * (size_t)CAPG * DEG);
    bestA = malloc(sizeof(int) * (size_t)CAPG * DEG);
    stamp = calloc(2 * (size_t)CAPG, sizeof(int));
    dist = malloc(sizeof(int) * 2 * (size_t)CAPG);
    queue = malloc(sizeof(int) * 2 * (size_t)CAPG);
    if (!S || !Sinv || !mark || !nA || !nB || !bestA || !stamp || !dist || !queue) {
        printf("0 0\n");
        return 0;
    }

    int64_t goal = best0 / 2 + 1;
    if (goal < DEG + 1) goal = DEG + 1;

    while (now_s() - t0 < TL) {
        if (goal > CAPG) break;
        int kk = KCHOICE[rndint(NKC)];
        int64_t mmv = (goal + kk - 1) / kk;
        if (mmv < 2) mmv = 2;
        if (mmv * kk > CAPG) {
            kk = 1;
            mmv = goal;
        }
        int r = sample_r((int)mmv, kk);
        set_group((int)mmv, kk, r);
        if (G < DEG + 1) continue;
        memset(mark, 0, sizeof(int) * (size_t)G);
        for (int i = 0; i < DEG; i++) {
            int s;
            do {
                s = rndint(G);
            } while (mark[s]);
            mark[s] = 1;
            S[i] = s;
        }
        for (int i = 0; i < DEG; i++) set_col(i, S[i]);

        int64_t fc = 0;
        if (anneal(ITERS, t0 + TL, &fc)) {
            bestG = G;
            memcpy(bestA, nA, sizeof(int) * (size_t)G * DEG);
            have_best = 1;
            goal = (int64_t)G + G / 100 + 1;
        }
    }

    if (!have_best) {
        printf("0 0\n");
        return 0;
    }
    long long n = 2LL * bestG;
    long long m = (long long)bestG * DEG;
    printf("%lld %lld\n", n, m);
    for (int x = 0; x < bestG; x++) {
        for (int i = 0; i < DEG; i++) {
            printf("%d %d\n", x, bestG + bestA[x * DEG + i]);
        }
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as fallbacks and as start graphs.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


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
# Slack extension: add new vertices using spare degree, accepting only
# graphs that pass lib.is_valid. For regular graphs this is a no-op.
# ----------------------------------------------------------------------------

def _bipartition(n, adj):
    """Return the 2-colouring of the graph, or None if it is not bipartite."""
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
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add new vertices using spare degree; returns (n, edges), always valid."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                w = n
                cand = edges + [(v, w) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


# ----------------------------------------------------------------------------
# Main build.
#
# Order: trivial and exact cases, then the fallback K_{d,d} (valid for D >= 2),
# then W(q) for D >= 4, then the C bi-Cayley annealer, then slack extension.
# Every candidate passes lib.is_valid before it replaces the best graph.
#
# Timing: the C search gets the time up to time_limit - 6 s. Compilation and
# process start-up fit in the remaining margin.
# ----------------------------------------------------------------------------

_MAX_CAP = 2_000_000


def build(d, D, seed, time_limit):
    start = time.monotonic()
    hard_end = start + max(1.0, time_limit - 2.5)
    c_end = start + max(1.0, time_limit - 6.0)
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]
    if d == 2:
        n = 2 * D
        cyc = [(i, (i + 1) % n) for i in range(n)]
        if lib.is_valid(n, cyc, d, D):
            return n, cyc
        return lib.haar_graph(2, range(2))

    # Safe fallback: K_{d,d} has diameter 2 and is optimal for D = 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]
    if D == 2:
        return best

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions. The calibration case d = 3, D = 3 returns immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < c_end - 5.0:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Main search: bi-Cayley annealing, entirely in C.
    if d >= 3 and D >= 3:
        remaining = c_end - time.monotonic()
        if remaining > 3.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap // 2 >= d + 1:
                try:
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, best_n, cap, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                        timeout=max(1.0, hard_end - time.monotonic()),
                    )
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    # Use spare degree if any (no-op for regular graphs).
    if time.monotonic() < hard_end - 0.5:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, hard_end)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
