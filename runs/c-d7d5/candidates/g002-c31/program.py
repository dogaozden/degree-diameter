import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine 1 (lift search, from the parent): simulated annealing over the
# voltages of a bi-Cayley lift over Z_m x|_r Z_k2 (element (a, b) = a*k2 + b).
# Usage: prog d D K m k2 r seed slice_seconds
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(clock_t t0) {
    return (double)(clock() - t0) / (double)CLOCKS_PER_SEC;
}

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, dd = y % K2;
    long long t = (a + (long long)POWR[b] * c) % MM;
    return (int)(t * K2 + (b + dd) % K2);
}

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

static int cost_fn(void) {
    int dup = 0;
    for (int e1 = 0; e1 < NE; e1++)
        for (int e2 = e1 + 1; e2 < NE; e2++)
            if (dI[e1] == dI[e2] && dJ[e1] == dJ[e2] && dS[e1] == dS[e2]) dup++;

    memset(cnt, 0, sizeof(int) * (size_t)N);
    for (int e = 0; e < NE; e++) {
        int ba = dI[e] * G, bb = (K + dJ[e]) * G;
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            int a = ba + g, b = bb + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }

    int total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cur = fr, *nxt = nx;
        int fn = 1, reached = 1;
        cur[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cur[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nxt[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return total + PEN * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) {
        fprintf(stderr, "usage: prog d D K m k2 r seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DIAM < 1 || K < 1 || MM < 1 || K2 < 1 || K2 > 60) {
        printf("0 0\n");
        return 0;
    }
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    G = MM * K2;
    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    dI = malloc(sizeof(int) * NE);
    dJ = malloc(sizeof(int) * NE);
    dS = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    const int RL = 40000;

    while (!found && elapsed(t0) < slice) {
        for (int l = 0; l < DEG; l++) {
            for (int i = 0; i < K; i++) p[i] = i;
            for (int i = K - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int t = p[i]; p[i] = p[j]; p[j] = t;
            }
            for (int i = 0; i < K; i++) {
                dI[l * K + i] = i;
                dJ[l * K + i] = p[i];
            }
        }
        for (int e = 0; e < NE; e++) {
            dS[e] = rndint(G);
            set_perm(e);
        }
        int cur = cost_fn();
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = 2.0 * (1.0 - (double)it / RL) + 0.05;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K);
                int i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                int e1 = l * K + i1, e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                }
            } else {
                int e = rndint(NE);
                int old = dS[e];
                int ns = rndint(G);
                if (ns == old) continue;
                dS[e] = ns;
                set_perm(e);
                int nc = cost_fn();
                if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                    cur = nc;
                } else {
                    dS[e] = old;
                    set_perm(e);
                }
            }
            if (cur == 0) { found = 1; break; }
        }
    }

    if (found) {
        printf("%d %d\n", N, NE * G);
        for (int e = 0; e < NE; e++) {
            for (int g = 0; g < G; g++) {
                printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
            }
        }
    } else {
        printf("0 0\n");
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# C engine 2 (new): grow-and-repair. Input is a valid bipartite graph with max
# degree d. Each attempt adds one A-vertex and one B-vertex, taking a matching
# of d edges out of the graph and rewiring it to the two new vertices (degrees
# are preserved). Then simulated annealing with degree-preserving double-edge
# switches minimises the number of vertex pairs at distance > D, counted
# exactly with bitset BFS. Success keeps the larger graph; failure restores the
# best one. Output is always the best valid graph found, or "0 0".
# Usage: prog d D seed slice_seconds      (graph on stdin, "n m" + edges)
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

static int DG, DIAM, NCAP, WCAP, N, W, bestN;
static int *deg, *adjl, *side, *usedA, *usedB, *bdeg, *badj, *bside, *qbuf;
static uint64_t *RA, *RB;
static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(clock_t t0) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

/* Number of unordered vertex pairs at distance > DIAM (unreachable counts too). */
static long eval_cost(void) {
    W = (N + 63) >> 6;
    uint64_t *cur = RA, *nxt = RB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * W);
            const int *av = adjl + (size_t)v * DG;
            for (int k = 0; k < deg[v]; k++) {
                const uint64_t *su = cur + (size_t)av[k] * W;
                for (int w = 0; w < W; w++) o[w] |= su[w];
            }
        }
        uint64_t *t = cur; cur = nxt; nxt = t;
    }
    long bad = 0;
    for (int v = 0; v < N; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += popc(s[w]);
        bad += N - c;
    }
    return bad / 2;
}

static int has_edge(int a, int b) {
    const int *l = adjl + (size_t)a * DG;
    for (int k = 0; k < deg[a]; k++) if (l[k] == b) return 1;
    return 0;
}
static void repl(int v, int old, int nw) {
    int *l = adjl + (size_t)v * DG;
    for (int k = 0; k < deg[v]; k++) if (l[k] == old) { l[k] = nw; return; }
}
static void del_from(int v, int old) {
    int *l = adjl + (size_t)v * DG;
    for (int k = 0; k < deg[v]; k++) {
        if (l[k] == old) { l[k] = l[deg[v] - 1]; deg[v]--; return; }
    }
}
static void add_to(int v, int nb) {
    adjl[(size_t)v * DG + deg[v]] = nb;
    deg[v]++;
}

/* (a1,b1),(a2,b2) -> (a1,b2),(a2,b1). Undo with sw_apply(a1,b2,a2,b1). */
static void sw_apply(int a1, int b1, int a2, int b2) {
    repl(a1, b1, b2);
    repl(b1, a1, a2);
    repl(a2, b2, b1);
    repl(b2, a2, a1);
}

static int rand_edge(int *ea, int *eb) {
    for (int tries = 0; tries < 1000; tries++) {
        int v = rndint(N);
        if (deg[v] == 0) continue;
        int u = adjl[(size_t)v * DG + rndint(deg[v])];
        if (side[v] == 0) { *ea = v; *eb = u; } else { *ea = u; *eb = v; }
        return 1;
    }
    return 0;
}

/* Add a new A vertex and a new B vertex, moving a matching of DG edges onto them. */
static int insert_pair(void) {
    if (N + 2 > NCAP) return 0;
    memset(usedA, 0, sizeof(int) * N);
    memset(usedB, 0, sizeof(int) * N);
    int ya[64], xb[64];
    int cnt = 0;
    long tries = 0;
    while (cnt < DG && tries < 200000) {
        tries++;
        int a, b;
        if (!rand_edge(&a, &b)) break;
        if (usedA[a] || usedB[b]) continue;
        usedA[a] = 1; usedB[b] = 1;
        ya[cnt] = a; xb[cnt] = b; cnt++;
    }
    if (cnt < DG) return 0;
    int A = N, B = N + 1;
    side[A] = 0; side[B] = 1;
    deg[A] = 0; deg[B] = 0;
    for (int i = 0; i < cnt; i++) {
        del_from(ya[i], xb[i]);
        del_from(xb[i], ya[i]);
        add_to(A, xb[i]);
        add_to(xb[i], A);
        add_to(B, ya[i]);
        add_to(ya[i], B);
    }
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed slice\n");
        return 1;
    }
    DG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0xABCDEFULL;
    if (rs == 0) rs = 1;

    if (DG < 1 || DG > 60 || DIAM < 1) { printf("0 0\n"); return 0; }
    int n, m;
    if (scanf("%d %d", &n, &m) != 2 || n <= 0 || m < 0 || n > 200000) {
        printf("0 0\n");
        return 0;
    }
    NCAP = n + 1200;
    WCAP = (NCAP + 63) >> 6;
    deg = calloc(NCAP, sizeof(int));
    adjl = malloc(sizeof(int) * (size_t)NCAP * DG);
    side = malloc(sizeof(int) * NCAP);
    usedA = malloc(sizeof(int) * NCAP);
    usedB = malloc(sizeof(int) * NCAP);
    bdeg = malloc(sizeof(int) * NCAP);
    badj = malloc(sizeof(int) * (size_t)NCAP * DG);
    bside = malloc(sizeof(int) * NCAP);
    qbuf = malloc(sizeof(int) * NCAP);
    RA = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    RB = malloc(sizeof(uint64_t) * (size_t)NCAP * WCAP);
    if (!deg || !adjl || !side || !usedA || !usedB || !bdeg || !badj || !bside || !qbuf || !RA || !RB) {
        printf("0 0\n");
        return 0;
    }

    N = n;
    int ok = 1;
    for (int i = 0; i < m; i++) {
        int u, v;
        if (scanf("%d %d", &u, &v) != 2) { ok = 0; break; }
        if (u < 0 || v < 0 || u >= n || v >= n || u == v || deg[u] >= DG || deg[v] >= DG) { ok = 0; break; }
        add_to(u, v);
        add_to(v, u);
    }
    if (!ok) { printf("0 0\n"); return 0; }

    /* Bipartition by BFS; reject non-bipartite input. */
    for (int v = 0; v < N; v++) side[v] = -1;
    int bip = 1;
    for (int s = 0; s < N && bip; s++) {
        if (side[s] != -1) continue;
        side[s] = 0;
        int h = 0, t = 0;
        qbuf[t++] = s;
        while (h < t && bip) {
            int v = qbuf[h++];
            for (int k = 0; k < deg[v]; k++) {
                int u = adjl[(size_t)v * DG + k];
                if (side[u] == -1) { side[u] = 1 - side[v]; qbuf[t++] = u; }
                else if (side[u] == side[v]) { bip = 0; break; }
            }
        }
    }
    if (!bip) { printf("0 0\n"); return 0; }

    if (eval_cost() != 0) { printf("0 0\n"); return 0; }

    bestN = N;
    memcpy(bdeg, deg, sizeof(int) * N);
    memcpy(badj, adjl, sizeof(int) * (size_t)N * DG);
    memcpy(bside, side, sizeof(int) * N);

    clock_t t0 = clock();
    const int ITER = 3000;
    while (elapsed(t0) < slice) {
        if (bestN + 2 > NCAP) break;
        N = bestN;
        memcpy(deg, bdeg, sizeof(int) * N);
        memcpy(adjl, badj, sizeof(int) * (size_t)N * DG);
        memcpy(side, bside, sizeof(int) * N);
        if (!insert_pair()) continue;

        long cur = eval_cost();
        for (int it = 0; it < ITER && cur > 0; it++) {
            if ((it & 31) == 0 && elapsed(t0) >= slice) break;
            double frac = (double)it / ITER;
            double T = 1.5 * (1.0 - frac) + 0.05;
            int a1, b1, a2, b2;
            if (!rand_edge(&a1, &b1) || !rand_edge(&a2, &b2)) break;
            if (a1 == a2 || b1 == b2) continue;
            if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
            sw_apply(a1, b1, a2, b2);
            long nc = eval_cost();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                sw_apply(a1, b2, a2, b1);
            }
        }
        if (cur == 0) {
            bestN = N;
            memcpy(bdeg, deg, sizeof(int) * N);
            memcpy(badj, adjl, sizeof(int) * (size_t)N * DG);
            memcpy(bside, side, sizeof(int) * N);
        }
    }

    long m2 = 0;
    for (int v = 0; v < bestN; v++) m2 += bdeg[v];
    printf("%d %ld\n", bestN, m2 / 2);
    for (int v = 0; v < bestN; v++) {
        for (int k = 0; k < bdeg[v]; k++) {
            int u = badj[(size_t)v * DG + k];
            if (v < u) printf("%d %d\n", v, u);
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions.
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
# Group sampling and the driver.
# ----------------------------------------------------------------------------

def _sample_group(target, rng):
    """Return (m, k2, r) describing Z_m x|_r Z_k2 with order m*k2 >= target, or None."""
    for _ in range(200):
        k2 = rng.choice([1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36])
        m = max(2, -(-target // k2))
        r = 1
        if k2 > 1 and m > 2:
            cands = [c for c in range(2, m) if math.gcd(c, m) == 1 and pow(c, k2, m) == 1 % m]
            if cands:
                r = rng.choice(cands)
        return m, k2, r
    return None


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

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

    if D >= 3:
        # Phase 1: lift search gives a strong starting graph.
        lift_end = time.monotonic() + 0.45 * max(0.0, deadline - time.monotonic())
        while True:
            remaining = lift_end - time.monotonic()
            if remaining < 1.0:
                break
            slice_s = min(remaining, 6.0)
            k = rng.choice([1, 1, 2, 2, 3])
            base = best[0] // (2 * k)
            target = base + 1 + rng.randrange(0, max(2, base // 10 + 1))
            grp = _sample_group(target, rng)
            if grp is None:
                continue
            m, k2, r = grp
            try:
                out = lib.run_c(
                    C_LIFT,
                    [d, D, k, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                    timeout=slice_s + 10.0,
                )
            except RuntimeError:
                break
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

        # Phase 2 (new): grow-and-repair from the best graph found so far.
        grow_s = deadline - time.monotonic() - 1.0
        if grow_s >= 1.0 and best[0] > 0:
            try:
                out = lib.run_c(
                    C_GROW,
                    [d, D, rng.randrange(1, 10 ** 9), f"{grow_s:.2f}"],
                    stdin_graph=best,
                    timeout=grow_s + 10.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
