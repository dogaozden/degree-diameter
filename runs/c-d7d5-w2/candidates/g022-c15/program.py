import itertools
import math
import random
import time

import lib


# ----------------------------------------------------------------------------
# Engine: simulated annealing over the voltages and base matchings of a
# bi-lift over an arbitrary finite group given by its multiplication table.
#
# Base: K vertices per side, DEG perfect matchings (dart (i, j, s) joins
# A-fibre i to B-fibre j with voltage s). Lift: (i, g) ~ (K+j, g*s).
# Left multiplication is an automorphism, so BFS from one vertex per fibre
# checks every pair. Cost = excess distance beyond DIAM plus unreached weight,
# plus a penalty for duplicate darts. Zero cost means a valid simple graph.
#
# Usage: prog DEG DIAM K seed slice_seconds
# stdin: the group table as a graph text "G M" followed by M pairs whose
#        flat sequence of 2M ints starts with the G*G table entries (row-major,
#        identity = element 0).
# stdout: a valid graph ("n m" + edges) or "0 0".
# ----------------------------------------------------------------------------

GROUP_LIFT_C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define STAG 8000
#define MAXD 8
#define MAXK 12

static int DEG, DIAM, K, G, N, NE;
static int *mt;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx, *bestS, *bestJ;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static clock_t T0C;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0C) / (double)CLOCKS_PER_SEC; }

static void set_perm(int e) {
    int s = dS[e];
    int *pm = perm + (size_t)e * G;
    for (int g = 0; g < G; g++) pm[g] = mt[(size_t)g * G + s];
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

static void save_best(void) {
    memcpy(bestS, dS, sizeof(int) * (size_t)NE);
    memcpy(bestJ, dJ, sizeof(int) * (size_t)NE);
}

int main(int argc, char **argv) {
    T0C = clock();
    if (argc < 6) { printf("0 0\n"); return 0; }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    K = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);

    int m_in = 0;
    if (scanf("%d %d", &G, &m_in) != 2 ||
        DEG < 1 || DEG > MAXD || DIAM < 1 || K < 1 || K > MAXK || G < 1 || m_in < 0) {
        printf("0 0\n");
        return 0;
    }
    long long need = (long long)G * G;
    long long tot = 2LL * m_in;
    if (tot < need || need > 4000000LL) { printf("0 0\n"); return 0; }
    mt = malloc(sizeof(int) * (size_t)need);
    if (!mt) { printf("0 0\n"); return 0; }
    int bad = 0;
    for (long long i = 0; i < tot; i++) {
        int x;
        if (scanf("%d", &x) != 1) { bad = 1; break; }
        if (i < need) {
            if (x < 0 || x >= G) bad = 1;
            else mt[i] = x;
        }
    }
    if (bad) { printf("0 0\n"); return 0; }
    for (int y = 0; y < G; y++) {
        if (mt[y] != y) { printf("0 0\n"); return 0; }
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;

    N = 2 * K * G;
    NE = DEG * K;
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

    int found = 0;
    int bestCost = BIGCOST;
    const int RL = 60000;

    while (!found && elapsed() < slice) {
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

        int runBest = cur;
        int since = 0;
        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && elapsed() >= slice) break;
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
            if (cur < runBest) { runBest = cur; since = 0; }
            else if (++since > STAG) break;
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
# Groups given as multiplication tables (identity = index 0).
# ----------------------------------------------------------------------------

_TABLE_CACHE = {}


def _psl_pgl_table(p, full):
    """Multiplication table of PSL(2,p) (full=False) or PGL(2,p) (full=True), identity first."""
    key = ("pgl" if full else "psl", p)
    if key in _TABLE_CACHE:
        return _TABLE_CACHE[key]

    def canon(M):
        if full:
            return min(tuple((x * t) % p for x in M) for t in range(1, p))
        neg = tuple((-x) % p for x in M)
        return min(M, neg)

    reps = set()
    for M in itertools.product(range(p), repeat=4):
        det = (M[0] * M[3] - M[1] * M[2]) % p
        if det == 0 or (not full and det != 1):
            continue
        reps.add(canon(M))
    ident = canon((1, 0, 0, 1))
    reps = [ident] + sorted(r for r in reps if r != ident)
    index = {r: i for i, r in enumerate(reps)}
    table = []
    for x in reps:
        a, b, c, d = x
        for y in reps:
            e, f, g, h = y
            prod = ((a * e + b * g) % p, (a * f + b * h) % p,
                    (c * e + d * g) % p, (c * f + d * h) % p)
            table.append(index[canon(prod)])
    res = (len(reps), table)
    _TABLE_CACHE[key] = res
    return res


def _table_groups():
    """Non-abelian groups tried as lift groups (name, order, lazy builder)."""
    return [
        ("psl2_11", 660, lambda: _psl_pgl_table(11, False)),
        ("pgl2_7", 336, lambda: _psl_pgl_table(7, True)),
        ("psl2_7", 168, lambda: _psl_pgl_table(7, False)),
    ]


def _semidirect_for(G, rng):
    """Return (m, k2, r) with m * k2 = G describing Z_m x|_r Z_k2 (r = 1 is the direct product)."""
    divs = [k for k in range(1, min(G, 64) + 1) if G % k == 0]
    for _ in range(50):
        k2 = rng.choice(divs)
        m = G // k2
        if k2 == 1 or m <= 2:
            return m, k2, 1
        cands = [r for r in range(2, m) if math.gcd(r, m) == 1 and pow(r, k2, m) == 1 % m]
        if cands and rng.random() < 0.7:
            return m, k2, rng.choice(cands)
        return m, k2, 1
    return G, 1, 1


# ----------------------------------------------------------------------------
# Exact starting points.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q <= d - 1."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


# ----------------------------------------------------------------------------
# Search driver.
# ----------------------------------------------------------------------------

G_CAP = 720  # keep group tables small enough to build in Python quickly


def _search(d, D, rng, state, deadline, groups):
    """Repeatedly run the group-lift annealer for larger orders; keep the best valid graph."""
    while True:
        rem = deadline - time.monotonic()
        if rem < 3.0:
            return
        n0 = state[0][0]
        K = rng.choice([1, 1, 1, 2, 2, 3, 4])
        bump = rng.choice([0.005, 0.01, 0.02, 0.04])
        target = n0 * (1.0 + bump) + 2
        opts = [g for g in groups if target <= 2 * K * g[1] <= 1.25 * target + 4]
        if opts and rng.random() < 0.6:
            _, order, builder = rng.choice(opts)
            order, table = builder()
        else:
            G = max(2, math.ceil(target / (2 * K)))
            if G > G_CAP:
                return
            m, k2, r = _semidirect_for(G, rng)
            order, mul, _ = lib.semidirect_group(m, k2, r)
            table = [mul(x, y) for x in range(order) for y in range(order)]

        if 2 * K * order > 2 * G_CAP * 4:
            continue

        rem = deadline - time.monotonic()
        if rem < 2.0:
            return
        slice_s = min(rem - 1.0, 8.0)
        flat = list(table)
        if len(flat) % 2:
            flat.append(0)
        pairs = list(zip(flat[0::2], flat[1::2]))
        try:
            out = lib.run_c(
                GROUP_LIFT_C_SOURCE,
                [d, D, K, rng.randrange(1, 10 ** 9), f"{slice_s:.2f}"],
                stdin_graph=(order, pairs),
                timeout=slice_s + 8.0,
            )
        except RuntimeError:
            return
        try:
            n, e = lib.parse_graph_text(out)
        except ValueError:
            continue
        if n > state[0][0] and lib.is_valid(n, e, d, D):
            state[0] = (n, e)


# ----------------------------------------------------------------------------
# Entry point.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(1.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if d == 1 or D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    state = [lib.haar_graph(d, range(d))]

    def consider(cand):
        try:
            n, e = cand
            if n > state[0][0] and lib.is_valid(n, e, d, D):
                state[0] = (n, e)
        except Exception:
            pass

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg)
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass
        if D == 3 and d - 1 >= 2 and lib.is_prime_power(d - 1):
            return state[0]

    if D >= 3 and 2 <= d <= 8:
        try:
            _search(d, D, rng, state, deadline, _table_groups())
        except Exception:
            pass

    best = state[0]
    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
