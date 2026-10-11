import itertools
import time

import lib


# ----------------------------------------------------------------------------
# C engine: bi-Cayley lift search over Z_m x|_r Z_k2 with K <= 2 base vertices
# per side and DEG layers. It combines:
#   * annealing with voltage moves and target-swap moves (K = 2),
#   * reheating from the group's best state with a random kick,
#   * exhaustive best-improvement coordinate polish near the end of a group,
#   * wall-clock deadlines, and strict improvement over min_n.
#
# Vertices: A_{i,g} = i*G+g, B_{j,h} = (K+j)*G+h. Dart e = l*K+i joins
# A_{i,g} to B_{dJ[e], g*dS[e]} for all g. Left multiplication is an automorphism,
# so BFS from the 2K representatives decides the diameter exactly.
# Cost = unreached (rep, vertex) pairs + PEN * duplicate darts; 0 is valid.
#
# Usage: prog DEG DIAM MIN_N seed slice_seconds
# Prints "n m" plus m edge lines for the best graph found, or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGCOST (1 << 30)
#define MAXDEG 64
#define MAXKK 2
#define MAXG 6000
#define MAXNE (MAXDEG * MAXKK)
#define MAXN (2 * MAXKK * MAXG)
#define MAXK2 64
#define ITERS 30000
#define POLISH_T 60
#define GROUP_T 6.0

static int DEG, DIAM, K, MM, K2, G, N, NE;
static int POWR[MAXK2];
static int dI[MAXNE], dJ[MAXNE], dS[MAXNE];
static int gJ[MAXNE], gS[MAXNE];
static int gbestCost;
static int perm[MAXNE * MAXG];
static int adj[MAXN * MAXDEG];
static int cnt[MAXN], fr[MAXN], nx[MAXN];
static uint32_t vis[MAXN];
static uint32_t stamp = 0;
static int outU[MAXNE * MAXG], outV[MAXNE * MAXG];
static int outN = 0, outM = 0;
static uint64_t rs = 88172645463325252ULL;

static inline uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static inline int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static inline double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcdll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static void set_group(int m, int k2, int r) {
    MM = m;
    K2 = k2;
    G = m * k2;
    POWR[0] = 1 % m;
    for (int b = 1; b < k2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, d = y % K2;
    long long t = ((long long)a + (long long)POWR[b] * (long long)c) % MM;
    return (int)(t * K2 + (b + d) % K2);
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
            if (cnt[a] < DEG && cnt[b] < DEG) {
                adj[(size_t)a * DEG + cnt[a]++] = b;
                adj[(size_t)b * DEG + cnt[b]++] = a;
            }
        }
    }

    long total = 0;
    for (int ri = 0; ri < 2 * K; ri++) {
        int src = ri * G;
        if (stamp == 0xFFFFFFFFu) {
            memset(vis, 0, sizeof(uint32_t) * (size_t)N);
            stamp = 0;
        }
        stamp++;
        vis[src] = stamp;
        int *cu = fr, *nu = nx;
        int fn = 1, reached = 1;
        cu[0] = src;
        for (int lv = 0; lv < DIAM && fn > 0; lv++) {
            int nn = 0;
            for (int q = 0; q < fn; q++) {
                int u = cu[q];
                const int *au = adj + (size_t)u * DEG;
                for (int t = 0; t < DEG; t++) {
                    int v = au[t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        nu[nn++] = v;
                    }
                }
            }
            reached += nn;
            int *tmp = cu;
            cu = nu;
            nu = tmp;
            fn = nn;
        }
        total += N - reached;
    }
    return (int)total + PEN * dup;
}

static void save_gbest(void) {
    memcpy(gJ, dJ, sizeof(int) * (size_t)NE);
    memcpy(gS, dS, sizeof(int) * (size_t)NE);
}

static void load_gbest(void) {
    memcpy(dJ, gJ, sizeof(int) * (size_t)NE);
    memcpy(dS, gS, sizeof(int) * (size_t)NE);
    for (int e = 0; e < NE; e++) set_perm(e);
}

static void random_init(void) {
    int p[MAXKK];
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) p[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < K; i++) {
            dI[l * K + i] = i;
            dJ[l * K + i] = p[i];
        }
    }
    for (int e = 0; e < NE; e++) dS[e] = rndint(G);
    for (int e = 0; e < NE; e++) set_perm(e);
}

static void kick_from_best(int kicks) {
    load_gbest();
    for (int q = 0; q < kicks; q++) {
        int e = rndint(NE);
        dS[e] = rndint(G);
        set_perm(e);
    }
}

/* Simulated annealing from the current state; tracks the group best. */
static int anneal(int iters, double T0, double limit) {
    int cur = cost_fn();
    if (cur < gbestCost) {
        gbestCost = cur;
        save_gbest();
    }
    for (int it = 0; it < iters && cur != 0; it++) {
        if ((it & 255) == 0 && now_s() > limit) break;
        double T = T0 * (1.0 - (double)it / (double)iters) + 0.05;
        if (K > 1 && rnd01() < 0.3) {
            int l = rndint(DEG);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int e1 = l * K + i1, e2 = l * K + i2;
            int t = dJ[e1];
            dJ[e1] = dJ[e2];
            dJ[e2] = t;
            int nc = cost_fn();
            if (nc <= cur || rnd01() < exp(-(double)(nc - cur) / T)) {
                cur = nc;
            } else {
                t = dJ[e1];
                dJ[e1] = dJ[e2];
                dJ[e2] = t;
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
        if (cur < gbestCost) {
            gbestCost = cur;
            save_gbest();
        }
    }
    return cur;
}

/* Best-improvement sweeps over single voltage changes, started from the group best. */
static void polish(double limit) {
    load_gbest();
    int cost = cost_fn();
    int improved = 1, stop = 0;
    while (improved && cost != 0 && !stop) {
        improved = 0;
        for (int e = 0; e < NE && cost != 0 && !stop; e++) {
            if (now_s() > limit) {
                stop = 1;
                break;
            }
            int old = dS[e], bestv = old, bestc = cost;
            for (int s = 0; s < G; s++) {
                if (s == old) continue;
                if ((s & 63) == 0 && now_s() > limit) {
                    stop = 1;
                    break;
                }
                dS[e] = s;
                set_perm(e);
                int c2 = cost_fn();
                if (c2 < bestc) {
                    bestc = c2;
                    bestv = s;
                }
            }
            dS[e] = bestv;
            set_perm(e);
            if (bestv != old) {
                cost = bestc;
                improved = 1;
            }
        }
    }
    cost = cost_fn();
    if (cost < gbestCost) {
        gbestCost = cost;
        save_gbest();
    }
}

static void sample_group(long long target, int *oM, int *oK2, int *oR) {
    static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 15, 16,
                             18, 20, 21, 24, 28, 30, 32, 36, 40};
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    int k = KF[rndint(nk)];
    long long m = (target + k - 1) / k;
    if (m < 2) m = 2;
    int r = 1;
    if (k > 1 && m > 2) {
        for (int t = 0; t < 300; t++) {
            long long c = 2 + (long long)rndint((int)(m - 2));
            if (gcdll(c, m) == 1 && powmod(c, k, m) == 1 % m) {
                r = (int)c;
                break;
            }
        }
    }
    *oM = (int)m;
    *oK2 = k;
    *oR = r;
}

static void record(void) {
    load_gbest();
    outN = N;
    outM = 0;
    for (int e = 0; e < NE; e++) {
        for (int g = 0; g < G; g++) {
            outU[outM] = dI[e] * G + g;
            outV[outM] = (K + dJ[e]) * G + perm[(size_t)e * G + g];
            outM++;
        }
    }
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    int minn = atoi(argv[3]);
    uint64_t seed = strtoull(argv[4], NULL, 10);
    double slice = atof(argv[5]);
    if (DEG < 1 || DEG > MAXDEG || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= seed * 0x9E3779B97F4A7C15ULL + 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    double tend = now_s() + slice;
    int bestN = minn;
    int have = 0;

    while (now_s() < tend - 0.05) {
        int Kc = (rndint(100) < 75) ? 1 : 2;
        long long half = bestN / (2 * Kc);
        long long span = half / 25 + 6;
        long long target = half + 1 + (long long)rndint((int)span);
        int M, k2, R;
        sample_group(target, &M, &k2, &R);
        if ((long long)M * k2 > MAXG) continue;
        set_group(M, k2, R);
        K = Kc;
        G = M * k2;
        N = 2 * K * G;
        NE = DEG * K;
        if (N <= bestN) continue;

        gbestCost = BIGCOST;
        double gend = now_s() + GROUP_T;
        if (gend > tend) gend = tend;
        int found = 0, round = 0;
        while (!found && now_s() < gend) {
            if (round == 0) {
                random_init();
                anneal(ITERS, 2.0, gend);
            } else {
                kick_from_best(NE / 8 + 1);
                anneal(ITERS, 0.8, gend);
            }
            round++;
            if (gbestCost == 0) {
                found = 1;
                break;
            }
            if (gbestCost <= POLISH_T && now_s() < gend) {
                polish(gend);
                if (gbestCost == 0) {
                    found = 1;
                    break;
                }
            }
        }
        if (found) {
            record();
            bestN = N;
            have = 1;
        }
    }

    if (have) {
        printf("%d %d\n", outN, outM);
        for (int k = 0; k < outM; k++) printf("%d %d\n", outU[k], outV[k]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _araujo(d):
    """Araujo-Pardo and Lopez graph for q = d - 2 when q is a prime power >= 3; diameter 3."""
    q = d - 2
    if q >= 3 and lib.is_prime_power(q):
        return lib.araujo_lopez_graph(q)
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
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(0.5, min(0.85 * time_limit, time_limit - 5.0))
    deadline = start + budget

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
        try:
            al = _araujo(d)
        except Exception:
            al = None
        if al is not None:
            consider(al[0], al[1])

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C search: repeated slices, each seeded with the best order found so far.
    if d >= 3 and D >= 3:
        it = 0
        while True:
            remaining = deadline - time.monotonic()
            if remaining < 2.0:
                break
            slice_s = min(remaining - 1.0, 15.0)
            it += 1
            call_seed = (seed * 1000003 + it * 7919) % 2000000011 + 1
            try:
                out = lib.run_c(C_SOURCE, [d, D, best[0], call_seed, f"{slice_s:.2f}"],
                                timeout=slice_s + 5.0)
            except RuntimeError:
                break
            try:
                n, e = lib.parse_graph_text(out)
            except ValueError:
                continue
            consider(n, e)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
