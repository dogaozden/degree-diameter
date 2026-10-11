import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# New engine: late-acceptance hill climbing (LAHC) over the voltages of a
# bi-regular lift over Z_m x|_r Z_k2 (element (a, b) coded as a*k2 + b).
#
# This replaces the simulated-annealing restarts of the parent. The search
# space is the same family, but the acceptance rule is different: a candidate
# is accepted if it is no worse than the current cost OR no worse than the
# cost remembered HLEN steps ago. This lets the walk drift across plateaus
# that annealing tends to reject at low temperature.
#
# The lift is G-symmetric (left translation), so the cost only needs BFS
# from one representative per base vertex: 2K sources.
#
# Usage: prog d D K m k2 r seed slice_seconds
# Prints a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

LIFT_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGC (1 << 29)
#define HLEN 256
#define STAG 40000

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int *POWR;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int hist[HLEN];
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

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

/* Cost: BFS excess from the 2K representatives, plus a penalty per duplicate dart. */
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

    const int LMAX = DIAM + 3;
    const int UNREACH_W = LMAX - DIAM + 2;
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
        for (int lv = 0; lv < LMAX && fn > 0; lv++) {
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
            if (lv + 1 > DIAM) total += (lv + 1 - DIAM) * nn;
            int *tmp = cur; cur = nxt; nxt = tmp;
            fn = nn;
        }
        total += (N - reached) * UNREACH_W;
    }
    return total + PEN * dup;
}

int main(int argc, char **argv) {
    if (argc < 9) { printf("0 0\n"); return 1; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    MM = atoi(argv[4]);
    K2 = atoi(argv[5]);
    int r = atoi(argv[6]);
    uint64_t seed = strtoull(argv[7], NULL, 10);
    double slice = atof(argv[8]);

    if (DEG < 1 || DEG > 32 || DIAM < 1 || K < 1 || K > 8 || MM < 1 || K2 < 1 || K2 > 4096) {
        printf("0 0\n");
        return 0;
    }
    if ((long long)MM * K2 > 4000) { printf("0 0\n"); return 0; }
    G = MM * K2;
    if (gcd_int(r, MM) != 1) { printf("0 0\n"); return 0; }
    POWR = malloc(sizeof(int) * (size_t)K2);
    if (!POWR) { printf("0 0\n"); return 0; }
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    if (((long long)POWR[K2 - 1] * r) % MM != 1 % MM) { printf("0 0\n"); return 0; }

    N = 2 * K * G;
    NE = DEG * K;

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x5DEECE66DULL;
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

    while (!found && (double)(clock() - t0) / CLOCKS_PER_SEC < slice) {
        /* Random restart: one random permutation per layer, random voltages. */
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
        for (int h = 0; h < HLEN; h++) hist[h] = cur;
        if (cur == 0) { found = 1; break; }

        int runBest = cur;
        long since = 0;
        for (long it = 0; ; it++) {
            if ((it & 127) == 0 && (double)(clock() - t0) / CLOCKS_PER_SEC >= slice) break;
            int hv = (int)(it % HLEN);
            int kind = 0, e1 = 0, e2 = 0, oldS = 0;
            if (K > 1 && rnd01() < 0.3) {
                int l = rndint(DEG);
                int i1 = rndint(K), i2 = rndint(K - 1);
                if (i2 >= i1) i2++;
                e1 = l * K + i1;
                e2 = l * K + i2;
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
                kind = 1;
            } else {
                e1 = rndint(NE);
                oldS = dS[e1];
                int ns = rndint(G);
                if (ns == oldS) continue;
                dS[e1] = ns;
                set_perm(e1);
                kind = 0;
            }
            int nc = cost_fn();
            if (nc <= cur || nc <= hist[hv]) {
                cur = nc;
            } else if (kind == 1) {
                int t = dJ[e1]; dJ[e1] = dJ[e2]; dJ[e2] = t;
            } else {
                dS[e1] = oldS;
                set_perm(e1);
            }
            hist[hv] = cur;
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
            if (cur == 0) { found = 1; break; }
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", N, NE * G);
    for (int e = 0; e < NE; e++) {
        const int *pm = perm + (size_t)e * G;
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + pm[g]);
        }
    }
    fflush(stdout);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact / safe constructions (carried over from the parent).
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
# Group sampling and the lift search phase.
# ----------------------------------------------------------------------------

def _group_candidates(gmin, rng):
    """Pick (m, k2, r) for Z_m x|_r Z_k2 with order m*k2 in [gmin, ~1.03*gmin + 3].

    Non-abelian choices (r != 1) are preferred, since cyclic lifts stall lower.
    Returns None if no candidate exists.
    """
    hi = int(gmin * 1.03) + 3
    nonab, ab = [], []
    for k2 in range(1, 41):
        m_lo = max(2, -(-gmin // k2))
        m_hi = hi // k2
        for m in range(m_lo, m_hi + 1):
            if m * k2 < gmin or m * k2 > hi:
                continue
            if k2 == 1:
                ab.append((m, 1, 1))
                continue
            rr = [x for x in range(2, m) if math.gcd(x, m) == 1 and pow(x, k2, m) == 1 % m]
            if rr:
                nonab.append((m, k2, rng.choice(rr)))
            else:
                ab.append((m, k2, 1))  # direct product, always a valid group
    if nonab and rng.random() < 0.8:
        pool = nonab
    else:
        pool = ab or nonab
    if not pool:
        return None
    return rng.choice(pool)


def _lift_phase(d, D, rng, state, until):
    """LAHC lift search; each successful run replaces state[0] with a larger valid graph."""
    while True:
        rem = until - time.monotonic()
        if rem < 2.0:
            break
        slice_s = min(rem - 0.8, 6.0)
        K = rng.choice([1, 2, 2, 3, 3, 4])
        n_cur = state[0][0]
        # A lift with K base vertices per side has 2*K*G vertices.
        gmin = n_cur // (2 * K) + 1
        if rng.random() < 0.4:
            gmin += rng.randint(1, 3)
        grp = _group_candidates(gmin, rng)
        if grp is None:
            continue
        m, k2, r = grp
        try:
            out = lib.run_c(
                LIFT_C_SOURCE,
                [d, D, K, m, k2, r, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                timeout=slice_s + 5.0,
            )
        except RuntimeError:
            break
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if n > n_cur and lib.is_valid(n, e, d, D):
            state[0] = (n, e)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.9 * time_limit, time_limit - 4.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    state = [lib.haar_graph(d, range(d))]

    def consider(cand):
        n, e = cand
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
            if D == 3 and lib.is_prime_power(d - 1):
                return state[0]
        if D == 3:
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except (ValueError, Exception):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq)
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return state[0]

    # Main search: late-acceptance hill climbing over lift voltages.
    try:
        _lift_phase(d, D, rng, state, deadline - 1.0)
    except Exception:
        pass

    best = state[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
