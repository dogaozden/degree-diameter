import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact baselines (from the parents).
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
# C engine.
#
# Bi-Cayley lift over G = Z_MM x|_R Z_K2 (element (a,b) coded a*K2+b), with
# K base vertices per side and DEG layers. Each layer is a permutation of the
# K base vertices. Dart e = l*K + i joins A_{i,g} to B_{dJ[e], g*dS[e]}.
# Left multiplication is an automorphism, so BFS from the 2K identity
# representatives decides the diameter exactly.
#
# Cost = unreached (rep, vertex) pairs + PEN * duplicate darts. Cost 0 = valid.
#
# Search: random group orders just above the current best order, a group
# anneal with reheating from the group's best state, and a best-improvement
# polish when the cost is small. Every success raises the bar.
#
# Usage: prog DEG DIAM seed slice_seconds min_n
# Prints the largest valid graph found ("n m" + edges), or "0 0".
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define PEN 1000
#define BIGC (1 << 30)
#define MAXKB 3
#define GMAX 4000
#define POLISH_T 80
#define RL 30000

static int DEG, DIAM;
static int K, G, MM, K2, N, NE;
static int POWR[64];
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *fr, *nx;
static int *bJ, *bS, *fJ, *fS;
static uint32_t *vis;
static uint32_t stamp = 0;
static uint64_t rs = 88172645463325252ULL;
static int maxNE, maxN;

static uint64_t rnd64(void) {
    rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17;
    return rs;
}
static int rndint(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcd_ll(long long a, long long b) {
    while (b) { long long t = a % b; a = b; b = t; }
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

static void setup_group(int kk, int mm, int k2, int r) {
    K = kk; MM = mm; K2 = k2;
    G = mm * k2;
    N = 2 * K * G;
    NE = DEG * K;
    POWR[0] = 1 % MM;
    for (int b = 1; b < K2; b++) POWR[b] = (int)((long long)POWR[b - 1] * r % MM);
    for (int e = 0; e < NE; e++) dI[e] = e % K;
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
    memcpy(bJ, dJ, sizeof(int) * (size_t)NE);
    memcpy(bS, dS, sizeof(int) * (size_t)NE);
}

static void load_best(void) {
    memcpy(dJ, bJ, sizeof(int) * (size_t)NE);
    memcpy(dS, bS, sizeof(int) * (size_t)NE);
    for (int e = 0; e < NE; e++) set_perm(e);
}

static void random_init(void) {
    int p[MAXKB];
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
}

/* Best-improvement sweeps over every single voltage value. */
static int polish(double gdl) {
    int cost = cost_fn();
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int e = 0; e < NE && cost != 0; e++) {
            if (now_s() >= gdl) return cost;
            int old = dS[e], bestv = old, bestc = cost;
            for (int s = 0; s < G; s++) {
                if (s == old) continue;
                dS[e] = s;
                set_perm(e);
                int c2 = cost_fn();
                if (c2 < bestc) { bestc = c2; bestv = s; }
                if (now_s() >= gdl) break;
            }
            dS[e] = bestv;
            set_perm(e);
            if (bestv != old) {
                cost = bestc;
                improved = 1;
            }
        }
    }
    return cost;
}

/* Anneal the current group with reheating. Returns 1 if a valid lift was found;
   the best state is then in bJ/bS. */
static int run_group(double gdl) {
    int bestCost = BIGC;
    int found = 0;
    while (!found && now_s() < gdl) {
        double T0;
        if (bestCost >= BIGC || rnd01() < 0.3) {
            random_init();
            T0 = 2.0;
        } else {
            memcpy(dJ, bJ, sizeof(int) * (size_t)NE);
            memcpy(dS, bS, sizeof(int) * (size_t)NE);
            int kick = NE / 8 + 1;
            for (int q = 0; q < kick; q++) dS[rndint(NE)] = rndint(G);
            for (int e = 0; e < NE; e++) set_perm(e);
            T0 = 0.8;
        }
        int cur = cost_fn();
        if (cur < bestCost) { bestCost = cur; save_best(); }
        if (cur == 0) { found = 1; break; }

        for (int it = 0; it < RL; it++) {
            if ((it & 255) == 0 && now_s() >= gdl) break;
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

        if (!found && bestCost > 0 && bestCost <= POLISH_T && now_s() < gdl) {
            load_best();
            int pc = polish(gdl);
            if (pc < bestCost) { bestCost = pc; save_best(); }
            if (pc == 0) found = 1;
        }
    }
    return found;
}

int main(int argc, char **argv) {
    if (argc < 6) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t seed = strtoull(argv[3], NULL, 10);
    double slice = atof(argv[4]);
    int min_n = atoi(argv[5]);
    if (DEG < 1 || DEG > 64 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }

    rs = seed * 0x9E3779B97F4A7C15ULL ^ 0x1234567ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    maxNE = DEG * MAXKB;
    maxN = 2 * MAXKB * GMAX;
    dI = malloc(sizeof(int) * maxNE);
    dJ = malloc(sizeof(int) * maxNE);
    dS = malloc(sizeof(int) * maxNE);
    bJ = malloc(sizeof(int) * maxNE);
    bS = malloc(sizeof(int) * maxNE);
    fJ = malloc(sizeof(int) * maxNE);
    fS = malloc(sizeof(int) * maxNE);
    perm = malloc(sizeof(int) * (size_t)maxNE * GMAX);
    adj = malloc(sizeof(int) * (size_t)maxN * DEG);
    cnt = malloc(sizeof(int) * maxN);
    fr = malloc(sizeof(int) * maxN);
    nx = malloc(sizeof(int) * maxN);
    vis = calloc((size_t)maxN, sizeof(uint32_t));
    if (!dI || !dJ || !dS || !bJ || !bS || !fJ || !fS || !perm || !adj ||
        !cnt || !fr || !nx || !vis) {
        printf("0 0\n");
        return 0;
    }

    static const int KF[] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16,
                             18, 20, 24, 30, 36};
    int nkf = (int)(sizeof(KF) / sizeof(KF[0]));

    double t_end = now_s() + slice;
    int best_n = min_n;
    int have = 0;
    int fK = 1, fMM = 1, fK2 = 1, fR = 1;

    while (now_s() < t_end - 0.3) {
        int kk;
        int pick = rndint(100);
        if (pick < 60) kk = 1;
        else if (pick < 90) kk = 2;
        else kk = 3;

        long long g0 = (long long)best_n / (2 * kk) + 1;
        long long span = g0 / 20 + 4;
        long long target = g0 + (long long)rndint((int)span);
        int k2 = KF[rndint(nkf)];
        long long mm = (target + k2 - 1) / k2;
        if (mm < 2) mm = 2;
        if (mm * k2 > GMAX) continue;

        int R = 1;
        if (k2 > 1 && mm > 2) {
            for (int t = 0; t < 300; t++) {
                long long c = 2 + (long long)rndint((int)(mm - 2));
                if (gcd_ll(c, mm) == 1 && powmod(c, k2, mm) == 1 % mm) {
                    R = (int)c;
                    break;
                }
            }
        }

        setup_group(kk, (int)mm, k2, R);
        if (N <= best_n) continue;

        double remaining = t_end - now_s();
        double gbud = remaining / 8.0;
        if (gbud < 1.0) gbud = 1.0;
        if (gbud > 5.0) gbud = 5.0;
        double gdl = now_s() + gbud;
        if (gdl > t_end) gdl = t_end;

        if (run_group(gdl)) {
            memcpy(fJ, bJ, sizeof(int) * (size_t)NE);
            memcpy(fS, bS, sizeof(int) * (size_t)NE);
            fK = K; fMM = MM; fK2 = K2; fR = R;
            best_n = N;
            have = 1;
        }
    }

    if (!have) {
        printf("0 0\n");
        fflush(stdout);
        return 0;
    }

    setup_group(fK, fMM, fK2, fR);
    memcpy(dJ, fJ, sizeof(int) * (size_t)NE);
    memcpy(dS, fS, sizeof(int) * (size_t)NE);
    for (int e = 0; e < NE; e++) set_perm(e);
    printf("%d %d\n", N, NE * G);
    for (int e = 0; e < NE; e++) {
        for (int g = 0; g < G; g++) {
            printf("%d %d\n", dI[e] * G + g, (K + dJ[e]) * G + perm[(size_t)e * G + g]);
        }
    }
    fflush(stdout);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions first, then the C search.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(2.0, min(0.85 * time_limit, time_limit - 6.0))
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

        # Araujo-Pardo and Lopez record for D = 3, d = q + 2.
        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except (ValueError, RuntimeError):
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C search, seeded with the best order found so far as a lower bound.
    if d >= 3 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(
                    C_SOURCE,
                    [d, D, int(seed) & 0x7FFFFFFF, f"{c_budget:.2f}", best[0]],
                    timeout=c_budget + 8.0,
                )
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
