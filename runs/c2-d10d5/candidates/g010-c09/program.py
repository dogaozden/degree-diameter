import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Bold rewrite: a two-phase C engine.
#
# Phase A (voltage search): bi-Cayley lifts over Z_M x|_r Z_K2 with K <= 4 base
#   blocks per side. Simulated annealing over voltages and block permutations.
#   The cost counts pairs of (vertex, identity-of-block) at distance > D, plus a
#   penalty for duplicate darts. Left-translation invariance makes this exact.
#
# Phase B (edge-split growth, NEW): starting from the best graph so far, insert
#   two new vertices a (side 0) and b (side 1). Pick DEG pairwise disjoint edges
#   (p_i, q_i), remove them, and join a to all q_i and b to all p_i. Every old
#   vertex keeps its degree and the graph stays bipartite and simple. Accept the
#   insertion only if the full diameter bound D still holds, checked with
#   bitsets. Each accepted step keeps the graph valid, so the output is always
#   valid.
#
# Start graph: exact constructions (PG(2,q), W(q)) when they apply, else K_{d,d}.
# Calibration cases (d=3, D=3) return the exact graph immediately.
# Python re-checks the output with lib.is_valid and falls back to a valid graph.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXK 4
#define MAXDEG 16
#define PEN 1000

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

static double T0c, TLIM, TEND_A;
static double now_s(void) {
    return (double)clock() / CLOCKS_PER_SEC - T0c;
}

static int DEG, DIAM, CAP;
static unsigned char POP[256];

/* current graph (phase B works on it; phase A writes its result here) */
static int gn;
static int *gnb, *gdeg;
static unsigned char *gside;   /* 0/1 = side, 2 = uncolored */

/* voltage state */
static int K, K2, M, R, G, VN;
static int PW[32];
static int lay[MAXDEG * MAXK], vol[MAXDEG * MAXK];
static int *vnb, *vcnt;
static unsigned char *rch, *rch2;

/* bitset buffers for the diameter check */
static uint64_t *bcur, *bnxt;
static int *stampv;
static int stampc;

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
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

/* group element x = a*K2 + b, (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int ax = x / K2, bx = x - ax * K2;
    int ay = y / K2, by = y - ay * K2;
    int64_t a2 = ((int64_t)ax + (int64_t)PW[bx] * ay) % M;
    int b2 = (bx + by) % K2;
    return (int)(a2 * K2 + b2);
}

static const int KCH[12] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 8, 10, 12};

static int sample_group(int64_t target) {
    for (int att = 0; att < 100; att++) {
        int k2 = KCH[rndint(12)];
        int64_t m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m > 2000000) return 0;
        int64_t r = 1;
        if (k2 > 1) {
            r = -1;
            for (int t = 0; t < 80; t++) {
                int64_t c = (m > 2) ? 2 + rndint((int)(m - 2)) : 1;
                if (gcd64(c, m) == 1 && powmod(c, k2, m) == 1 % m) {
                    r = c;
                    break;
                }
            }
            if (r < 0) continue;
        }
        K2 = k2;
        M = (int)m;
        R = (int)r;
        G = M * K2;
        return 1;
    }
    return 0;
}

/* Darts: layer l, block i maps A-block i to B-block lay[l*K+i] with voltage vol[l*K+i].
   Each layer is a permutation of blocks, so every vertex gets exactly DEG edges. */
static void build_voltage(void) {
    int n = 2 * K * G;
    VN = n;
    memset(vcnt, 0, sizeof(int) * (size_t)n);
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) {
            int p = lay[l * K + i], s = vol[l * K + i];
            for (int g = 0; g < G; g++) {
                int a = i * G + g;
                int b = (K + p) * G + gmul(g, s);
                vnb[a * DEG + vcnt[a]++] = b;
                vnb[b * DEG + vcnt[b]++] = a;
            }
        }
    }
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l = 0; l < DEG; l++)
            for (int l2 = l + 1; l2 < DEG; l2++)
                if (lay[l * K + i] == lay[l2 * K + i] && vol[l * K + i] == vol[l2 * K + i])
                    c++;
    return c;
}

/* Cost = number of (vertex, block-identity) pairs at distance > DIAM, plus duplicates.
   By left-translation invariance, cost 0 iff the lift has diameter <= DIAM. */
static int64_t voltage_cost(void) {
    build_voltage();
    int n = VN;
    for (int v = 0; v < n; v++) rch[v] = 0;
    for (int c = 0; c < 2 * K; c++) rch[c * G] = (unsigned char)(1u << c);
    for (int t = 0; t < DIAM; t++) {
        int changed = 0;
        for (int v = 0; v < n; v++) {
            unsigned char x = rch[v];
            for (int k = 0; k < DEG; k++) x |= rch[vnb[v * DEG + k]];
            rch2[v] = x;
            if (x != rch[v]) changed = 1;
        }
        unsigned char *tmp = rch;
        rch = rch2;
        rch2 = tmp;
        if (!changed) break;
    }
    int64_t unr = 0;
    for (int v = 0; v < n; v++) unr += 2 * K - POP[rch[v]];
    return unr + (int64_t)PEN * dupcount();
}

static int anneal(int iters) {
    int ne = DEG * K;
    for (int l = 0; l < DEG; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i];
            perm[i] = perm[j];
            perm[j] = t;
        }
        for (int i = 0; i < K; i++) lay[l * K + i] = perm[i];
    }
    for (int e = 0; e < ne; e++) vol[e] = rndint(G);

    int64_t cost = voltage_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    int bl[MAXDEG * MAXK], bv[MAXDEG * MAXK];
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && now_s() > TEND_A) return 0;
        memcpy(bl, lay, sizeof(int) * (size_t)ne);
        memcpy(bv, vol, sizeof(int) * (size_t)ne);
        if (K > 1 && rnd01() < 0.3) {
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tp = lay[l * K + i1];
            lay[l * K + i1] = lay[l * K + i2];
            lay[l * K + i2] = tp;
        } else {
            int e = rndint(ne);
            vol[e] = rndint(G);
        }
        int64_t c2 = voltage_cost();
        double temp = 0.03 * c0 * (1.0 - (double)t / iters) + 0.3;
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
        } else {
            memcpy(lay, bl, sizeof(int) * (size_t)ne);
            memcpy(vol, bv, sizeof(int) * (size_t)ne);
        }
    }
    return cost == 0;
}

static void voltage_phase(void) {
    while (now_s() < TEND_A) {
        int k = 1 + rndint(MAXK);
        int64_t gmin = gn / (2 * k) + 1;
        int span = gn / (8 * k) + 2;
        int64_t target = gmin + rndint(span);
        if (!sample_group(target)) continue;
        int64_t N = 2LL * k * G;
        if (N <= gn || N > CAP) continue;
        K = k;
        for (int t = 0; t < K2; t++) PW[t] = (int)powmod(R, t, M);
        if (anneal(3000)) {
            build_voltage();   /* rebuild from the accepted state */
            gn = VN;
            memcpy(gnb, vnb, sizeof(int) * (size_t)DEG * (size_t)gn);
            for (int v = 0; v < gn; v++) {
                gdeg[v] = DEG;
                gside[v] = (unsigned char)((v / G) >= K ? 1 : 0);
            }
        }
    }
}

/* Full diameter check on the current graph (bitsets over vertices). */
static int diam_ok(int n) {
    if (n < 1) return 1;
    int W = (n + 63) / 64;
    for (int v = 0; v < n; v++) {
        uint64_t *row = bcur + (size_t)v * W;
        memset(row, 0, sizeof(uint64_t) * (size_t)W);
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = bnxt + (size_t)v * W;
            const uint64_t *src = bcur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int k = 0; k < gdeg[v]; k++) {
                const uint64_t *nbr = bcur + (size_t)gnb[v * DEG + k] * W;
                for (int j = 0; j < W; j++) dst[j] |= nbr[j];
            }
        }
        uint64_t *tmp = bcur;
        bcur = bnxt;
        bnxt = tmp;
    }
    int rem = n & 63;
    uint64_t last = rem ? ((1ULL << rem) - 1) : ~0ULL;
    for (int v = 0; v < n; v++) {
        const uint64_t *row = bcur + (size_t)v * W;
        for (int j = 0; j < W - 1; j++)
            if (row[j] != ~0ULL) return 0;
        if (row[W - 1] != last) return 0;
    }
    return 1;
}

/* Edge-split growth: insert two vertices a (side 0) and b (side 1) per step. */
static void growth(void) {
    int pp[MAXDEG], qq[MAXDEG], sp[MAXDEG], sr[MAXDEG];
    while (gn >= 2 && gn + 2 <= CAP && now_s() < TLIM) {
        stampc++;
        int cnt = 0, tries = 0;
        while (cnt < DEG && tries < 400) {
            tries++;
            int p = rndint(gn);
            if (gside[p] != 0 || gdeg[p] == 0) continue;
            int k = rndint(gdeg[p]);
            int q = gnb[p * DEG + k];
            if (stampv[p] == stampc || stampv[q] == stampc) continue;
            stampv[p] = stampc;
            stampv[q] = stampc;
            pp[cnt] = p;
            qq[cnt] = q;
            sp[cnt] = k;
            cnt++;
        }
        if (cnt < DEG) continue;

        int ok = 1;
        for (int i = 0; i < cnt && ok; i++) {
            int p = pp[i], q = qq[i];
            int s = -1;
            for (int j = 0; j < gdeg[q]; j++) {
                if (gnb[q * DEG + j] == p) {
                    s = j;
                    break;
                }
            }
            if (s < 0) ok = 0;
            else sr[i] = s;
            (void)p;
        }
        if (!ok) continue;

        int a = gn, b = gn + 1;
        gside[a] = 0;
        gside[b] = 1;
        gdeg[a] = DEG;
        gdeg[b] = DEG;
        for (int i = 0; i < DEG; i++) {
            int p = pp[i], q = qq[i];
            gnb[p * DEG + sp[i]] = b;
            gnb[q * DEG + sr[i]] = a;
            gnb[a * DEG + i] = q;
            gnb[b * DEG + i] = p;
        }
        gn += 2;
        if (diam_ok(gn)) continue;

        /* revert */
        gn -= 2;
        for (int i = 0; i < DEG; i++) {
            int p = pp[i], q = qq[i];
            gnb[p * DEG + sp[i]] = q;
            gnb[q * DEG + sr[i]] = p;
        }
    }
}

/* 2-colour the input graph; returns 0 if it is not bipartite. */
static int color_graph(void) {
    for (int v = 0; v < gn; v++) gside[v] = 2;
    int *queue = malloc(sizeof(int) * (size_t)(gn > 0 ? gn : 1));
    if (!queue) return 0;
    int ok = 1;
    for (int s = 0; s < gn && ok; s++) {
        if (gside[s] != 2) continue;
        gside[s] = 0;
        int qh = 0, qt = 0;
        queue[qt++] = s;
        while (qh < qt && ok) {
            int u = queue[qh++];
            for (int k = 0; k < gdeg[u]; k++) {
                int w = gnb[u * DEG + k];
                if (gside[w] == 2) {
                    gside[w] = (unsigned char)(1 - gside[u]);
                    queue[qt++] = w;
                } else if (gside[w] == gside[u]) {
                    ok = 0;
                    break;
                }
            }
        }
    }
    free(queue);
    return ok;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    CAP = atoi(argv[3]);
    unsigned long long seed = strtoull(argv[4], NULL, 10);
    double TL = atof(argv[5]);
    double gfrac = atof(argv[6]);

    T0c = (double)clock() / CLOCKS_PER_SEC;
    TLIM = TL;
    TEND_A = TL * (1.0 - gfrac);

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();
    for (int x = 0; x < 256; x++) {
        int c = 0;
        for (int y = x; y; y >>= 1) c += y & 1;
        POP[x] = (unsigned char)c;
    }

    if (DEG < 3 || DEG > MAXDEG || DIAM < 3 || CAP < 8 || CAP > 40000) {
        printf("0 0\n");
        return 0;
    }

    int W = (CAP + 63) / 64;
    gnb = malloc(sizeof(int) * (size_t)DEG * (size_t)CAP);
    gdeg = calloc((size_t)CAP, sizeof(int));
    gside = calloc((size_t)CAP, 1);
    vnb = malloc(sizeof(int) * (size_t)DEG * (size_t)CAP);
    vcnt = malloc(sizeof(int) * (size_t)CAP);
    rch = malloc((size_t)CAP);
    rch2 = malloc((size_t)CAP);
    bcur = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)W);
    bnxt = malloc(sizeof(uint64_t) * (size_t)CAP * (size_t)W);
    stampv = calloc((size_t)CAP, sizeof(int));
    if (!gnb || !gdeg || !gside || !vnb || !vcnt || !rch || !rch2 || !bcur || !bnxt || !stampv) {
        printf("0 0\n");
        return 0;
    }

    /* read the optional start graph */
    gn = 0;
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 > 0 && n0 <= CAP && m0 >= 0) {
        int ok = 1;
        for (int e = 0; e < m0; e++) {
            int u, v;
            if (scanf("%d %d", &u, &v) != 2) {
                ok = 0;
                break;
            }
            if (u < 0 || v < 0 || u >= n0 || v >= n0 || u == v) {
                ok = 0;
                break;
            }
            if (gdeg[u] >= DEG || gdeg[v] >= DEG) {
                ok = 0;
                break;
            }
            gnb[u * DEG + gdeg[u]++] = v;
            gnb[v * DEG + gdeg[v]++] = u;
        }
        gn = n0;
        if (!ok || !color_graph()) {
            gn = 0;
            memset(gdeg, 0, sizeof(int) * (size_t)CAP);
        }
    }

    voltage_phase();
    growth();

    long long m = 0;
    for (int v = 0; v < gn; v++) m += gdeg[v];
    m /= 2;
    if (gn == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %lld\n", gn, m);
    for (int v = 0; v < gn; v++)
        for (int k = 0; k < gdeg[v]; k++) {
            int w = gnb[v * DEG + k];
            if (v < w) printf("%d %d\n", v, w);
        }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as start graphs.
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
# Main build: exact start graph, then the two-phase C engine.
# ----------------------------------------------------------------------------

_MAX_CAP = 12_000  # bitset memory in C is cap^2 / 8 bytes per buffer


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.88 * time_limit, time_limit - 7.0))
    deadline = start + budget

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
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d >= 3 and D >= 3:
        remaining = deadline - time.monotonic()
        if remaining > 3.0:
            cap = min(lib.moore_bound(d, D), _MAX_CAP)
            if cap > best_n:
                try:
                    c_time = round(max(1.0, remaining - 2.5), 2)
                    text = lib.run_c(
                        C_SOURCE,
                        [d, D, cap, int(seed) & 0x7FFFFFFF, c_time, 0.5],
                        stdin_graph=best,
                        timeout=remaining + 20.0,
                    )
                    n2, e2 = lib.parse_graph_text(text)
                    consider(n2, e2)
                except Exception:
                    pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
