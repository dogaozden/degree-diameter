import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (unchanged): projective planes and generalized quadrangles.
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
# New approach: incremental growth by vertex pairs, with simulated annealing
# over degree-preserving 2-switches to remove all pairs at distance > D.
#
# Model: bipartite graph, side-0 vertices and side-1 vertices, edges stored as
# (ea, eb) with ea on side 0 and eb on side 1. Degrees are kept fixed by
# 2-switches, so the search space is the set of bipartite graphs with the same
# degree sequence. Cost = number of unordered pairs at distance > D, computed
# with bitset BFS.
#
# Growth step: pick k = d-1 edges x_i y_i with distinct x and distinct y,
# remove them, add a (side 0) joined to every y_i, b (side 1) joined to every
# x_i, and a-b. Degrees stay <= d and the order grows by 2. The annealer then
# tries to repair the diameter. An attempt that fails is rolled back to the
# last valid snapshot and retried with new random cuts.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>
#include <math.h>

static uint64_t rs = 88172645463325252ULL;

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd() % (uint64_t)n); }

static double rnd01(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static int popc(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int DG, DIAM, NCAP, WCAP, ECAP, N, M, HIN = 0;
static int *ea, *eb, *nb, *dg, *stA, *stB, *snapA, *snapB;
static unsigned char *adj;
static uint64_t *bufA, *bufB;
static int stamp = 0;
static int snapN, snapM;

static void adj_add(int u, int v) {
    if (dg[u] >= DG || dg[v] >= DG) {
        fprintf(stderr, "degree overflow\n");
        exit(1);
    }
    nb[(size_t)u * DG + dg[u]++] = v;
    nb[(size_t)v * DG + dg[v]++] = u;
    adj[(size_t)u * NCAP + v] = 1;
    adj[(size_t)v * NCAP + u] = 1;
    if (u + 1 > HIN) HIN = u + 1;
    if (v + 1 > HIN) HIN = v + 1;
}

static void rem_from(int u, int v) {
    int *L = nb + (size_t)u * DG;
    int k = dg[u];
    for (int i = 0; i < k; i++) {
        if (L[i] == v) {
            L[i] = L[k - 1];
            dg[u] = k - 1;
            return;
        }
    }
}

static void adj_remove(int u, int v) {
    rem_from(u, v);
    rem_from(v, u);
    adj[(size_t)u * NCAP + v] = 0;
    adj[(size_t)v * NCAP + u] = 0;
}

/* Edge e1 = (ea[e1], eb[e1]) and e2 = (ea[e2], eb[e2]) are replaced by
   (na1, nb1) and (na2, nb2). Degrees are preserved if the multiset of
   endpoints is preserved. */
static void switch2(int e1, int e2, int na1, int nb1, int na2, int nb2) {
    adj_remove(ea[e1], eb[e1]);
    adj_remove(ea[e2], eb[e2]);
    ea[e1] = na1;
    eb[e1] = nb1;
    ea[e2] = na2;
    eb[e2] = nb2;
    adj_add(na1, nb1);
    adj_add(na2, nb2);
}

static void rebuild(int n, int m, const int *sa, const int *sb) {
    for (int v = 0; v < HIN; v++) memset(adj + (size_t)v * NCAP, 0, (size_t)HIN);
    memset(dg, 0, sizeof(int) * (size_t)NCAP);
    HIN = 0;
    N = n;
    M = m;
    for (int e = 0; e < m; e++) {
        ea[e] = sa[e];
        eb[e] = sb[e];
        adj_add(sa[e], sb[e]);
    }
    if (n > HIN) HIN = n;
}

static void save_snap(void) {
    snapN = N;
    snapM = M;
    memcpy(snapA, ea, sizeof(int) * (size_t)M);
    memcpy(snapB, eb, sizeof(int) * (size_t)M);
}

/* Number of unordered pairs at distance > DIAM. Bitset BFS from every vertex. */
static long long cost_bad(void) {
    int W = (N + 63) / 64;
    uint64_t *cur = bufA, *nxt = bufB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)N * (size_t)W);
    for (int v = 0; v < N; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < N; v++) {
            uint64_t *o = nxt + (size_t)v * W;
            const uint64_t *s = cur + (size_t)v * W;
            memcpy(o, s, sizeof(uint64_t) * (size_t)W);
            int k = dg[v];
            const int *L = nb + (size_t)v * DG;
            for (int t = 0; t < k; t++) {
                const uint64_t *p = cur + (size_t)L[t] * W;
                for (int w = 0; w < W; w++) o[w] |= p[w];
            }
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
    }
    long long bad = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *s = cur + (size_t)v * W;
        int c = 0;
        for (int w = 0; w < W; w++) c += popc(s[w]);
        bad += N - c;
    }
    return bad / 2;
}

/* Simulated annealing over 2-switches until cost 0 or t_end. Returns 1 on success. */
static int anneal(double t_end) {
    double ts = now_s();
    double span = t_end - ts;
    if (span <= 0) span = 1e-6;
    long long cur = cost_bad();
    if (cur == 0) return 1;
    while (1) {
        double now = now_s();
        if (now >= t_end) break;
        double frac = (now - ts) / span;
        double T = 0.04 + 0.8 * (1.0 - frac) * (1.0 - frac);
        int e1 = rint_(M), e2 = rint_(M);
        if (e1 == e2) continue;
        int a1 = ea[e1], b1 = eb[e1], a2 = ea[e2], b2 = eb[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (adj[(size_t)a1 * NCAP + b2] || adj[(size_t)a2 * NCAP + b1]) continue;
        switch2(e1, e2, a1, b2, a2, b1);
        long long nc = cost_bad();
        long long delta = nc - cur;
        if (delta <= 0 || rnd01() < exp(-(double)delta / T)) {
            cur = nc;
            if (cur == 0) return 1;
        } else {
            switch2(e1, e2, a1, b1, a2, b2);
        }
    }
    return cur == 0;
}

/* Pair insertion by edge cutting on the current graph. */
static int grow_step(void) {
    int k = DG - 1;
    if (k < 1 || M < k || N + 2 > NCAP) return 0;
    int px[64], py[64], pe[64];
    int cnt = 0;
    stamp++;
    int tries = 0;
    while (cnt < k && tries < 200000) {
        tries++;
        int e = rint_(M);
        int x = ea[e], y = eb[e];
        if (stA[x] == stamp || stB[y] == stamp) continue;
        stA[x] = stamp;
        stB[y] = stamp;
        pe[cnt] = e;
        px[cnt] = x;
        py[cnt] = y;
        cnt++;
    }
    if (cnt < k) return 0;
    int a = N, b = N + 1;
    for (int i = 0; i < k; i++) adj_remove(px[i], py[i]);
    for (int i = 0; i < k; i++) {
        ea[pe[i]] = a;
        eb[pe[i]] = py[i];
        adj_add(a, py[i]);
        ea[M + i] = px[i];
        eb[M + i] = b;
        adj_add(px[i], b);
    }
    ea[M + k] = a;
    eb[M + k] = b;
    adj_add(a, b);
    M += k + 1;
    N += 2;
    return 1;
}

int main(int argc, char **argv) {
    DG = argc > 1 ? atoi(argv[1]) : 3;
    DIAM = argc > 2 ? atoi(argv[2]) : 3;
    unsigned long long seed = argc > 3 ? strtoull(argv[3], NULL, 10) : 1ULL;
    double tl = argc > 4 ? atof(argv[4]) : 10.0;
    NCAP = argc > 5 ? atoi(argv[5]) : 2000;
    if (DG < 2 || DG > 64 || DIAM < 2) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) {
        n0 = 0;
        m0 = 0;
    }
    if (n0 < 0 || m0 < 0) {
        printf("0 0\n");
        return 0;
    }
    int *iu = malloc(sizeof(int) * (size_t)(m0 + 1));
    int *iv = malloc(sizeof(int) * (size_t)(m0 + 1));
    if (n0 == 0) {
        /* No start graph given: start from K_{d,d}. */
        n0 = 2 * DG;
        m0 = DG * DG;
        free(iu);
        free(iv);
        iu = malloc(sizeof(int) * (size_t)(m0 + 1));
        iv = malloc(sizeof(int) * (size_t)(m0 + 1));
        int idx = 0;
        for (int i = 0; i < DG; i++)
            for (int j = 0; j < DG; j++) {
                iu[idx] = i;
                iv[idx] = DG + j;
                idx++;
            }
    } else {
        for (int i = 0; i < m0; i++) {
            if (scanf("%d %d", &iu[i], &iv[i]) != 2) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    if (n0 + 4 > NCAP) NCAP = n0 + 4;
    if (NCAP < 2 * DG + 4) NCAP = 2 * DG + 4;
    WCAP = (NCAP + 63) / 64;
    ECAP = NCAP * DG + 8;

    ea = malloc(sizeof(int) * (size_t)ECAP);
    eb = malloc(sizeof(int) * (size_t)ECAP);
    snapA = malloc(sizeof(int) * (size_t)ECAP);
    snapB = malloc(sizeof(int) * (size_t)ECAP);
    nb = malloc(sizeof(int) * (size_t)NCAP * (size_t)DG);
    dg = calloc((size_t)NCAP, sizeof(int));
    adj = calloc((size_t)NCAP * (size_t)NCAP, 1);
    stA = calloc((size_t)NCAP, sizeof(int));
    stB = calloc((size_t)NCAP, sizeof(int));
    bufA = malloc(sizeof(uint64_t) * (size_t)NCAP * (size_t)WCAP);
    bufB = malloc(sizeof(uint64_t) * (size_t)NCAP * (size_t)WCAP);
    int *col = malloc(sizeof(int) * (size_t)n0);
    int *deg0 = calloc((size_t)n0, sizeof(int));
    if (!ea || !eb || !snapA || !snapB || !nb || !dg || !adj || !stA || !stB ||
        !bufA || !bufB || !col || !deg0) {
        printf("0 0\n");
        return 0;
    }

    /* Validate the start graph and orient each edge as (side 0, side 1). */
    for (int i = 0; i < m0; i++) {
        int u = iu[i], v = iv[i];
        if (u < 0 || u >= n0 || v < 0 || v >= n0 || u == v) {
            printf("0 0\n");
            return 0;
        }
        deg0[u]++;
        deg0[v]++;
    }
    for (int v = 0; v < n0; v++)
        if (deg0[v] > DG) {
            printf("0 0\n");
            return 0;
        }
    for (int v = 0; v < n0; v++) col[v] = -1;
    for (int s = 0; s < n0; s++) {
        if (col[s] >= 0) continue;
        col[s] = 0;
        int changed = 1;
        while (changed) {
            changed = 0;
            for (int i = 0; i < m0; i++) {
                int u = iu[i], v = iv[i];
                if (col[u] >= 0 && col[v] < 0) {
                    col[v] = 1 - col[u];
                    changed = 1;
                } else if (col[v] >= 0 && col[u] < 0) {
                    col[u] = 1 - col[v];
                    changed = 1;
                }
            }
        }
    }
    for (int i = 0; i < m0; i++) {
        int u = iu[i], v = iv[i];
        if (col[u] == col[v]) {
            printf("0 0\n");
            return 0;
        }
        if (col[u] == 0) {
            snapA[i] = u;
            snapB[i] = v;
        } else {
            snapA[i] = v;
            snapB[i] = u;
        }
    }
    snapN = n0;
    snapM = m0;

    double t0 = now_s();
    double deadline = t0 + tl;

    rebuild(snapN, snapM, snapA, snapB);
    if (cost_bad() != 0) {
        if (!anneal(t0 + tl * 0.25)) {
            printf("0 0\n");
            return 0;
        }
        save_snap();
    }

    while (1) {
        double rem = deadline - now_s();
        if (rem < 0.2) break;
        if (snapN + 2 > NCAP) break;
        double att = rem / 40.0;
        if (att < 0.2) att = 0.2;
        if (att > rem) att = rem;
        rebuild(snapN, snapM, snapA, snapB);
        if (!grow_step()) continue;
        if (anneal(now_s() + att)) save_snap();
    }

    printf("%d %d\n", snapN, snapM);
    for (int e = 0; e < snapM; e++) printf("%d %d\n", snapA[e], snapB[e]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C growth search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    budget = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = t0 + budget

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

    # Growth search in C. The start graph is the best exact graph if it is
    # larger than K_{d,d}; otherwise C starts from K_{d,d} itself.
    if d >= 2 and D >= 2:
        left = deadline - time.monotonic() - 2.0
        if left >= 1.0:
            max_n = int(min(2600, max(lib.moore_bound(d, D), 2 * d + 4)))
            start_graph = best if best[0] > 2 * d else None
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{left:.2f}", max_n],
                                stdin_graph=start_graph, timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
