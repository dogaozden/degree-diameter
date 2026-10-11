import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: direct simulated annealing over bipartite graphs, with
# vertex-by-vertex growth. The graph has H vertices per side, identified as
# A_a = a and B_b = H + b. The search keeps max degree <= DEG and only changes
# edges by moves that preserve the simple bipartite structure:
#   - switch: (a1,b1),(a2,b2) -> (a1,b2),(a2,b1)
#   - move an A endpoint or a B endpoint of an edge to a deficient vertex
#   - add an edge between two deficient, non-adjacent vertices (never hurts)
# The cost is the number of unordered vertex pairs at distance > DIAM. It is
# evaluated exactly with bitset ball propagation. When cost reaches 0, the graph
# is recorded and grown by one vertex per side, then annealing continues.
# The best valid graph is printed. Python keeps the PG / K_{d,d} / W(q)
# baselines as fallbacks and validates every candidate.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXH 1024
#define MAXN (2 * MAXH)
#define MAXW (MAXN / 64)
#define PERIOD 3000
#define T_HI 1.5
#define T_LO 0.08
#define STEP_BUDGET 6000

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int pop64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DEG, DIAM;
static int H, ne;
static int *EU, *EV;          /* edge e joins A vertex EU[e] and B vertex EV[e] */
static unsigned char *adjm;   /* adjm[a*MAXH + b] = 1 if edge (a,b) exists */
static int *degA, *degB;
static int *adjl, *cntv;
static uint64_t *Rb, *NRb;
static int best_H = 0, best_ne = 0;
static int *bEU, *bEV;

/* Last applied move, for undo. */
static int mt;
static int m_e1, m_e2, m_a1, m_b1, m_a2, m_b2, m_x;

static void add_edge(int a, int b) {
    EU[ne] = a;
    EV[ne] = b;
    ne++;
    adjm[a * MAXH + b] = 1;
    degA[a]++;
    degB[b]++;
}

/* Number of unordered pairs at distance > DIAM (unreachable pairs included). */
static long long eval_bad(void) {
    int N = 2 * H, W = (N + 63) / 64;
    for (int v = 0; v < N; v++) cntv[v] = 0;
    for (int e = 0; e < ne; e++) {
        int u = EU[e], v = H + EV[e];
        adjl[(size_t)u * DEG + cntv[u]++] = v;
        adjl[(size_t)v * DEG + cntv[v]++] = u;
    }
    memset(Rb, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) Rb[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    uint64_t *R = Rb, *NR = NRb;
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *dst = NR + (size_t)v * W;
            const uint64_t *src = R + (size_t)v * W;
            for (int w = 0; w < W; w++) dst[w] = src[w];
            for (int k = 0; k < cntv[v]; k++) {
                const uint64_t *nb = R + (size_t)adjl[(size_t)v * DEG + k] * W;
                for (int w = 0; w < W; w++) dst[w] |= nb[w];
            }
        }
        uint64_t *t = R;
        R = NR;
        NR = t;
    }
    long long tot = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *src = R + (size_t)v * W;
        for (int w = 0; w < W; w++) c += pop64(src[w]);
        tot += N - c;
    }
    return tot / 2;
}

/* Propose one random move and apply it. Returns 1 if a move was applied. */
static int propose(void) {
    if (ne < 1) return 0;
    int r = rnd_int(100);
    if (r < 60) {
        if (ne < 2) return 0;
        int e1 = rnd_int(ne), e2 = rnd_int(ne);
        if (e1 == e2) return 0;
        int a1 = EU[e1], b1 = EV[e1], a2 = EU[e2], b2 = EV[e2];
        if (a1 == a2 || b1 == b2) return 0;
        if (adjm[a1 * MAXH + b2] || adjm[a2 * MAXH + b1]) return 0;
        adjm[a1 * MAXH + b1] = 0;
        adjm[a2 * MAXH + b2] = 0;
        adjm[a1 * MAXH + b2] = 1;
        adjm[a2 * MAXH + b1] = 1;
        EV[e1] = b2;
        EV[e2] = b1;
        mt = 1;
        m_e1 = e1; m_e2 = e2; m_a1 = a1; m_b1 = b1; m_a2 = a2; m_b2 = b2;
        return 1;
    } else if (r < 80) {
        int e = rnd_int(ne);
        int x = rnd_int(H);
        int a = EU[e], b = EV[e];
        if (degA[x] >= DEG || x == a || adjm[x * MAXH + b]) return 0;
        adjm[a * MAXH + b] = 0;
        adjm[x * MAXH + b] = 1;
        EU[e] = x;
        degA[a]--;
        degA[x]++;
        mt = 2;
        m_e1 = e; m_a1 = a; m_b1 = b; m_x = x;
        return 1;
    } else {
        int e = rnd_int(ne);
        int y = rnd_int(H);
        int a = EU[e], b = EV[e];
        if (degB[y] >= DEG || y == b || adjm[a * MAXH + y]) return 0;
        adjm[a * MAXH + b] = 0;
        adjm[a * MAXH + y] = 1;
        EV[e] = y;
        degB[b]--;
        degB[y]++;
        mt = 3;
        m_e1 = e; m_a1 = a; m_b1 = b; m_x = y;
        return 1;
    }
}

static void undo(void) {
    switch (mt) {
    case 1:
        adjm[m_a1 * MAXH + m_b2] = 0;
        adjm[m_a2 * MAXH + m_b1] = 0;
        adjm[m_a1 * MAXH + m_b1] = 1;
        adjm[m_a2 * MAXH + m_b2] = 1;
        EV[m_e1] = m_b1;
        EV[m_e2] = m_b2;
        break;
    case 2:
        adjm[m_x * MAXH + m_b1] = 0;
        adjm[m_a1 * MAXH + m_b1] = 1;
        EU[m_e1] = m_a1;
        degA[m_x]--;
        degA[m_a1]++;
        break;
    case 3:
        adjm[m_a1 * MAXH + m_x] = 0;
        adjm[m_a1 * MAXH + m_b1] = 1;
        EV[m_e1] = m_b1;
        degB[m_x]--;
        degB[m_b1]++;
        break;
    default:
        break;
    }
    mt = 0;
}

/* Add a random edge between two deficient, non-adjacent vertices. Never increases cost. */
static int try_fill_random(void) {
    int a = rnd_int(H), b = rnd_int(H);
    if (degA[a] < DEG && degB[b] < DEG && !adjm[a * MAXH + b] && ne < MAXH * DEG) {
        add_edge(a, b);
        return 1;
    }
    return 0;
}

/* Greedily add all possible edges between deficient vertices. */
static void fill_all(void) {
    for (int a = 0; a < H; a++) {
        if (degA[a] >= DEG) continue;
        for (int b = 0; b < H && degA[a] < DEG; b++) {
            if (degB[b] < DEG && !adjm[a * MAXH + b] && ne < MAXH * DEG) add_edge(a, b);
        }
    }
}

/* Simulated annealing at the current H. Returns 1 when cost reaches 0. */
static int anneal(long long steps) {
    long long cur = eval_bad();
    for (long long it = 0; it < steps; it++) {
        if (cur == 0) return 1;
        if ((it & 127) == 0 && elapsed() > DEADLINE) return 0;
        if (rnd_unit() < 0.02) {
            if (try_fill_random()) cur = eval_bad();
            continue;
        }
        double ph = (double)(it % PERIOD) / (double)PERIOD;
        double T = T_LO + (T_HI - T_LO) * (1.0 - ph);
        if (!propose()) continue;
        long long c2 = eval_bad();
        long long d = c2 - cur;
        if (d <= 0 || rnd_unit() < exp(-(double)d / T)) {
            cur = c2;
        } else {
            undo();
        }
    }
    return cur == 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    EU = malloc(sizeof(int) * (size_t)MAXH * DEG);
    EV = malloc(sizeof(int) * (size_t)MAXH * DEG);
    bEU = malloc(sizeof(int) * (size_t)MAXH * DEG);
    bEV = malloc(sizeof(int) * (size_t)MAXH * DEG);
    adjm = calloc((size_t)MAXH * MAXH, 1);
    degA = calloc(MAXH, sizeof(int));
    degB = calloc(MAXH, sizeof(int));
    adjl = malloc(sizeof(int) * (size_t)MAXN * DEG);
    cntv = malloc(sizeof(int) * (size_t)MAXN);
    Rb = malloc(sizeof(uint64_t) * (size_t)MAXN * MAXW);
    NRb = malloc(sizeof(uint64_t) * (size_t)MAXN * MAXW);

    mt = 0;
    H = 1;
    ne = 0;
    fill_all();
    while (elapsed() < DEADLINE) {
        if (anneal(STEP_BUDGET)) {
            best_H = H;
            best_ne = ne;
            memcpy(bEU, EU, sizeof(int) * (size_t)ne);
            memcpy(bEV, EV, sizeof(int) * (size_t)ne);
            if (H + 1 > MAXH) break;
            H++;
            fill_all();
        }
    }

    if (best_H > 0) {
        printf("%d %d\n", 2 * best_H, best_ne);
        for (int e = 0; e < best_ne; e++)
            printf("%d %d\n", bEU[e], best_H + bEV[e]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families.
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
# Driver: baselines in Python, then the C annealer with growth.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - start < 0.2 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave margin for compilation, parsing and validation.
    remaining = 0.85 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}"],
                            timeout=remaining + 10.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
