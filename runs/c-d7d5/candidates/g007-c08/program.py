import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Stage 1 engine (seed): simulated annealing over voltages of bi-Cayley lifts
# over Z_m x|_r Z_k2. Produces a valid bipartite graph used as the start point.
# Usage: prog d D K m k2 r seed slice_seconds   (prints "n m" + edges or "0 0")
# ----------------------------------------------------------------------------

C_LIFT = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bestS, *bestJ;
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

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
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
    bestS = malloc(sizeof(int) * NE);
    bestJ = malloc(sizeof(int) * NE);
    perm = malloc(sizeof(int) * (size_t)NE * G);
    adj = malloc(sizeof(int) * (size_t)N * DEG);
    cnt = malloc(sizeof(int) * N);
    fr = malloc(sizeof(int) * N);
    nx = malloc(sizeof(int) * N);
    vis = calloc(N, sizeof(uint32_t));
    int *p = malloc(sizeof(int) * K);
    if (!dI || !dJ || !dS || !bestS || !bestJ || !perm || !adj || !cnt || !fr || !nx || !vis || !p) {
        printf("0 0\n");
        return 0;
    }

    clock_t t0 = clock();
    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed(t0) < slice) {
        double T0;
        if (bestCost >= BIGCOST || rnd01() < 0.25) {
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
            T0 = 2.0;
        } else {
            memcpy(dJ, bestJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bestS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed(t0) >= slice) break;
            double T = T0 * (1.0 - (double)it / RL) + 0.05;
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
            if (cur < bestCost) { bestCost = cur; save_best(); }
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
# Stage 2 engine (grow): edge-switch repair search that adds vertex pairs.
#
# Input: a valid bipartite graph (stdin, "n m" + edges). Each growth step adds a
# fresh pair (anew in side A, bnew in side B). Their DEG edges are created by
# subdividing DEG old edges, which keeps every old degree unchanged. Then
# simulated annealing with degree-preserving switches (swap the B-endpoints of
# two edges) drives the number of ordered pairs at distance > D to zero.
# Distances come from bit-parallel ball expansion over D rounds.
# The output is the largest graph reached with zero bad pairs.
# Usage: prog d D seed slice_seconds
# ----------------------------------------------------------------------------

C_GROW = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define MAXE (MAXN * 64)
#define MAXDEG 64
#define CYCLE 5000

static int DEG, DIAM;
static int n, NE;
static int ea[MAXE], eb[MAXE];
static int bestEA[MAXE], bestEB[MAXE], bestNE, bestN;
static int sbEA[MAXE], sbEB[MAXE], sbNE;
static int dg[MAXN];
static int adj[MAXN * MAXDEG];
static uint64_t R1[MAXN * MAXW], R2[MAXN * MAXW];
static int markA[MAXN], markB[MAXN];
static int stampv = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t t0;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int m) { return (int)(rnd64() % (uint64_t)m); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) { return (double)(clock() - t0) / (double)CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int exists_edge(int a, int b) {
    for (int e = 0; e < NE; e++)
        if (ea[e] == a && eb[e] == b) return 1;
    return 0;
}

static void rebuild_adj(void) {
    memset(dg, 0, sizeof(int) * (size_t)n);
    for (int e = 0; e < NE; e++) {
        int a = ea[e], b = eb[e];
        adj[a * DEG + dg[a]++] = b;
        adj[b * DEG + dg[b]++] = a;
    }
}

/* Number of ordered pairs (v, w) with dist(v, w) > DIAM. */
static long eval_bad(void) {
    rebuild_adj();
    int W = (n + 63) >> 6;
    uint64_t *cur = R1, *nxt = R2;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + (v >> 6)] |= 1ULL << (v & 63);
    for (int t = 0; t < DIAM; t++) {
        for (int v = 0; v < n; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *c = cur + (size_t)v * W;
            memcpy(o, c, sizeof(uint64_t) * W);
            for (int k = 0; k < dg[v]; k++) {
                const uint64_t *cu = cur + (size_t)adj[v * DEG + k] * W;
                for (int w = 0; w < W; w++) o[w] |= cu[w];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long bad = 0;
    for (int v = 0; v < n; v++) {
        const uint64_t *c = cur + (size_t)v * W;
        int cnt = 0;
        for (int w = 0; w < W; w++) cnt += pc64(c[w]);
        bad += n - cnt;
    }
    return bad;
}

/* Add fresh A vertex n and fresh B vertex n+1, each with DEG edges taken by
   subdividing DEG old edges (x,y) into (x,bnew) and (anew,y). All x distinct and
   all y distinct, so no duplicate edges arise and old degrees are unchanged. */
static int add_pair(void) {
    int nold = n, anew = n, bnew = n + 1;
    if (n + 2 > MAXN || NE + DEG > MAXE) return 0;
    stampv++;
    for (int k = 0; k < DEG; k++) {
        int idx = -1;
        for (int tries = 0; tries < 200000; tries++) {
            int c = rndint(NE);
            int x = ea[c], y = eb[c];
            if (x >= nold || y >= nold) continue;
            if (markA[x] == stampv || markB[y] == stampv) continue;
            idx = c;
            break;
        }
        if (idx < 0) return 0;
        int x = ea[idx], y = eb[idx];
        markA[x] = stampv;
        markB[y] = stampv;
        eb[idx] = bnew;
        ea[NE] = anew;
        eb[NE] = y;
        NE++;
    }
    n += 2;
    return 1;
}

static void save_work(int *EA, int *EB, int *cnt) {
    memcpy(EA, ea, sizeof(int) * (size_t)NE);
    memcpy(EB, eb, sizeof(int) * (size_t)NE);
    *cnt = NE;
}

static void load_work(const int *EA, const int *EB, int cnt) {
    memcpy(ea, EA, sizeof(int) * (size_t)cnt);
    memcpy(eb, EB, sizeof(int) * (size_t)cnt);
    NE = cnt;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed slice\n");
        return 1;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) { printf("0 0\n"); return 0; }
    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
    if (rs == 0) rs = 1;
    t0 = clock();

    int n0, m0;
    if (scanf("%d %d", &n0, &m0) != 2 || n0 < 1 || n0 > MAXN - 2 || m0 < 0 || m0 > MAXE / 2) {
        printf("0 0\n");
        return 0;
    }
    int *U = malloc(sizeof(int) * (m0 + 1));
    int *V = malloc(sizeof(int) * (m0 + 1));
    for (int i = 0; i < m0; i++) {
        if (scanf("%d %d", &U[i], &V[i]) != 2) { printf("0 0\n"); return 0; }
        if (U[i] < 0 || U[i] >= n0 || V[i] < 0 || V[i] >= n0 || U[i] == V[i]) {
            printf("0 0\n");
            return 0;
        }
    }

    /* Bipartition by BFS (CSR adjacency). */
    int *cd = calloc(n0 + 1, sizeof(int));
    for (int i = 0; i < m0; i++) { cd[U[i]]++; cd[V[i]]++; }
    for (int v = 0; v < n0; v++) if (cd[v] > DEG) { printf("0 0\n"); return 0; }
    int *st = malloc(sizeof(int) * (n0 + 1));
    st[0] = 0;
    for (int v = 0; v < n0; v++) st[v + 1] = st[v] + cd[v];
    int *fl = malloc(sizeof(int) * (n0 + 1));
    memcpy(fl, st, sizeof(int) * (n0 + 1));
    int *nb = malloc(sizeof(int) * (2 * m0 + 1));
    for (int i = 0; i < m0; i++) {
        nb[fl[U[i]]++] = V[i];
        nb[fl[V[i]]++] = U[i];
    }
    int *col = malloc(sizeof(int) * n0);
    for (int v = 0; v < n0; v++) col[v] = -1;
    int *qu = malloc(sizeof(int) * n0);
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int qh = 0, qt = 0;
        qu[qt++] = s;
        while (qh < qt) {
            int u = qu[qh++];
            for (int k = st[u]; k < st[u + 1]; k++) {
                int w = nb[k];
                if (col[w] < 0) { col[w] = 1 - col[u]; qu[qt++] = w; }
                else if (col[w] == col[u]) { printf("0 0\n"); return 0; }
            }
        }
    }

    n = n0;
    NE = 0;
    for (int i = 0; i < m0; i++) {
        if (col[U[i]] == 0) { ea[NE] = U[i]; eb[NE] = V[i]; }
        else                { ea[NE] = V[i]; eb[NE] = U[i]; }
        NE++;
    }

    if (eval_bad() != 0) { printf("0 0\n"); return 0; }

    bestN = n;
    bestNE = NE;
    memcpy(bestEA, ea, sizeof(int) * (size_t)NE);
    memcpy(bestEB, eb, sizeof(int) * (size_t)NE);

    while (elapsed() < slice) {
        n = bestN;
        load_work(bestEA, bestEB, bestNE);
        if (!add_pair()) break;

        long cur = eval_bad();
        long sbCost = cur;
        save_work(sbEA, sbEB, &sbNE);
        int found = (cur == 0);
        long it = 0;

        while (!found) {
            if ((it & 31) == 0 && elapsed() >= slice) break;
            if (it > 0 && it % CYCLE == 0) {
                load_work(sbEA, sbEB, sbNE);
                cur = sbCost;
            }
            double T = 3.0 * (1.0 - (double)(it % CYCLE) / CYCLE) + 0.2;
            it++;
            int i = rndint(NE), j = rndint(NE);
            if (i == j) continue;
            int a1 = ea[i], b1 = eb[i], a2 = ea[j], b2 = eb[j];
            if (a1 == a2 || b1 == b2) continue;
            if (exists_edge(a1, b2) || exists_edge(a2, b1)) continue;
            eb[i] = b2;
            eb[j] = b1;
            long nc = eval_bad();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
                if (cur < sbCost) {
                    sbCost = cur;
                    save_work(sbEA, sbEB, &sbNE);
                }
                if (cur == 0) found = 1;
            } else {
                eb[i] = b1;
                eb[j] = b2;
            }
        }

        if (!found) break;
        bestN = n;
        bestNE = NE;
        memcpy(bestEA, ea, sizeof(int) * (size_t)NE);
        memcpy(bestEB, eb, sizeof(int) * (size_t)NE);
    }

    printf("%d %d\n", bestN, bestNE);
    for (int e = 0; e < bestNE; e++) printf("%d %d\n", bestEA[e], bestEB[e]);
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions and helpers.
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


# ----------------------------------------------------------------------------
# Pipeline stages.
# ----------------------------------------------------------------------------

def _seed_lift(d, D, rng, best, deadline):
    """Use the voltage-lift annealer to find a large valid start graph."""
    failures = 0
    while failures < 3:
        remaining = deadline - time.monotonic()
        if remaining < 1.0:
            break
        slice_s = min(remaining, 10.0)
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
            failures += 1
            continue
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)
    return best


def _grow(d, D, rng, best, deadline):
    """Grow the start graph by vertex pairs with the edge-switch repair annealer."""
    slice_s = deadline - time.monotonic()
    if slice_s < 1.0:
        return best
    try:
        out = lib.run_c(
            C_GROW,
            [d, D, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
            stdin_graph=best,
            timeout=slice_s + 15.0,
        )
    except RuntimeError:
        return best
    try:
        n, e = lib.parse_graph_text(out)
    except ValueError:
        return best
    if n > best[0] and lib.is_valid(n, e, d, D):
        return (n, e)
    return best


def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    seed_deadline = start + 0.3 * budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for D >= 2.
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

    if D >= 4:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Stage 1: lift-based seed. Stage 2: vertex-pair growth by edge-switch repair.
    best = _seed_lift(d, D, rng, best, seed_deadline)
    best = _grow(d, D, rng, best, deadline)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
