import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact constructions (fallbacks and starting points).
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
# C engine: bi-Cayley lifts over Z_m x|_r Z_k2 (element (a, b) coded a*k2+b).
#
# Base: K vertices per side, DEG layers. Each layer l is a permutation P[l][.]
# with voltage S[l][i]: dart (l, i) joins A_{i,g} to B_{P[l][i], g*s}.
# Left multiplication is an automorphism, so BFS from the 2K representatives
# decides the diameter exactly. Cost = weighted unreached (rep, vertex) pairs
# + PEN * duplicate darts; cost 0 means valid.
#
# Search per group: breakout local search (clause-weight bumping on unreached
# pairs, STUCK-triggered), then reheats from the group's best state with a
# random kick, then a unit-weight coordinate polish when close to 0.
# The group order is always above the best order found so far, and every
# valid graph raises that bar. The best valid graph is printed at the end.
#
# Usage: prog d D seed time_limit [min_n]
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <time.h>

#define MAXD 64
#define MAXK 3
#define GMAX 4000
#define NVMAX (2 * MAXK * GMAX)
#define PEN 1000
#define STUCK 60
#define BREAK_ITERS 20000
#define REHEAT_TRIES 3
#define REHEAT_MAX 400
#define POLISH_T 60

static int DEG = 3, DIAM = 3;
static int K = 1, G = 1, MM = 1, K2 = 1, NV = 2;
static int POWR[64];
static int P[MAXD][MAXK], S[MAXD][MAXK];
static int BP[MAXD][MAXK], BS[MAXD][MAXK];
static int GP[MAXD][MAXK], GS[MAXD][MAXK];
static int RP[MAXD][MAXK], RS[MAXD][MAXK];
static int PM[MAXD][MAXK][GMAX];
static int adj[NVMAX * MAXD];
static int cnt[NVMAX];
static int vis[NVMAX];
static int qbuf[NVMAX];
static int stamp = 0;
static long long W[2 * MAXK * NVMAX];
static long long g_raw = 0;
static uint64_t rs = 88172645463325252ULL;
static double deadline = 0.0;
static int candbuf[GMAX + 1];

static uint64_t rnd64(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rint_(int n) { return (int)(rnd64() % (uint64_t)n); }

static double now_s(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)ts.tv_sec + 1e-9 * (double)ts.tv_nsec;
}

static long long gcd_ll(long long a, long long b) {
    while (b) {
        long long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long long powmod_ll(long long b, long long e, long long m) {
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

static void set_group(int M, int k2, int r) {
    MM = M;
    K2 = k2;
    G = M * k2;
    long long p = 1 % M;
    for (int b = 0; b < k2; b++) {
        POWR[b] = (int)p;
        p = (p * r) % M;
    }
}

static void setperm(int l, int i) {
    int s = S[l][i];
    for (int g = 0; g < G; g++) PM[l][i][g] = gmul(g, s);
}

static void setall(void) {
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++) setperm(l, i);
}

static void reset_weights(void) {
    long long tot = (long long)2 * K * NV;
    for (long long j = 0; j < tot; j++) W[j] = 1;
}

/* Weighted cost (sum of weights of unreached pairs + PEN * duplicates).
   g_raw receives the unweighted cost. If bump != 0, the weight of every
   currently unreached pair grows by one. */
static long long cost_eval(int bump) {
    int dup = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < DEG; l1++)
            for (int l2 = l1 + 1; l2 < DEG; l2++)
                if (P[l1][i] == P[l2][i] && S[l1][i] == S[l2][i]) dup++;

    for (int v = 0; v < NV; v++) cnt[v] = 0;
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) {
            int j = P[l][i];
            int ba = i * G, bb = (K + j) * G;
            for (int g = 0; g < G; g++) {
                int a = ba + g, b = bb + PM[l][i][g];
                adj[a * DEG + cnt[a]++] = b;
                adj[b * DEG + cnt[b]++] = a;
            }
        }
    }

    long long wsum = 0, raw = 0;
    for (int r = 0; r < 2 * K; r++) {
        if (stamp >= 0x3fffffff) {
            memset(vis, 0, sizeof(vis));
            stamp = 0;
        }
        stamp++;
        int src = r * G;
        int head = 0, tail = 0;
        vis[src] = stamp;
        qbuf[tail++] = src;
        for (int lv = 0; lv < DIAM; lv++) {
            int end = tail;
            if (head == end) break;
            while (head < end) {
                int u = qbuf[head++];
                for (int t = 0; t < DEG; t++) {
                    int v = adj[u * DEG + t];
                    if (vis[v] != stamp) {
                        vis[v] = stamp;
                        qbuf[tail++] = v;
                    }
                }
            }
        }
        long long *w = W + (size_t)r * (size_t)NV;
        for (int v = 0; v < NV; v++) {
            if (vis[v] != stamp) {
                raw++;
                wsum += w[v];
                if (bump) w[v]++;
            }
        }
    }
    g_raw = raw + (long long)PEN * dup;
    return wsum + (long long)PEN * dup;
}

static void save_cur(void) {
    memcpy(BP, P, sizeof(P));
    memcpy(BS, S, sizeof(S));
}

static void load_best(void) {
    memcpy(P, BP, sizeof(P));
    memcpy(S, BS, sizeof(S));
    setall();
}

static void random_cfg(void) {
    for (int l = 0; l < DEG; l++) {
        for (int i = 0; i < K; i++) P[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rint_(i + 1);
            int t = P[l][i];
            P[l][i] = P[l][j];
            P[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rint_(G);
    }
    setall();
}

/* Breakout local search; leaves P,S at the best raw-cost state seen. */
static long long breakout(long iters) {
    reset_weights();
    long long wc = cost_eval(0);
    long long bestraw = g_raw;
    save_cur();
    int stuck = 0;
    for (long t = 0; t < iters && wc != 0; t++) {
        if ((t & 63) == 0 && now_s() > deadline) break;
        int l = rint_(DEG), i = rint_(K);
        int kind = (K >= 2 && rint_(4) == 0);
        int i2 = 0, olds = 0;
        if (kind) {
            i2 = rint_(K - 1);
            if (i2 >= i) i2++;
            int tmp = P[l][i];
            P[l][i] = P[l][i2];
            P[l][i2] = tmp;
        } else {
            olds = S[l][i];
            int ns = rint_(G);
            if (ns == olds) continue;
            S[l][i] = ns;
            setperm(l, i);
        }
        long long wc2 = cost_eval(0);
        if (wc2 <= wc) {
            if (wc2 < wc) stuck = 0;
            else stuck++;
            wc = wc2;
            if (g_raw < bestraw) {
                bestraw = g_raw;
                save_cur();
            }
        } else {
            if (kind) {
                int tmp = P[l][i];
                P[l][i] = P[l][i2];
                P[l][i2] = tmp;
            } else {
                S[l][i] = olds;
                setperm(l, i);
            }
            stuck++;
        }
        if (stuck >= STUCK) {
            cost_eval(1);          /* raise weights of unreached pairs */
            wc = cost_eval(0);
            stuck = 0;
        }
    }
    load_best();
    return bestraw;
}

/* Best-improvement coordinate sweeps over voltages with unit weights. */
static long long polish(void) {
    reset_weights();
    long long cost = cost_eval(0);
    int improved = 1;
    while (improved && cost != 0) {
        improved = 0;
        for (int l = 0; l < DEG && cost != 0; l++) {
            for (int i = 0; i < K && cost != 0; i++) {
                if (now_s() > deadline) return cost;
                int old = S[l][i];
                int bestv = old;
                long long bestc = cost;
                for (int s = 0; s < G; s++) {
                    if (s == old) continue;
                    S[l][i] = s;
                    setperm(l, i);
                    long long c2 = cost_eval(0);
                    if (c2 < bestc) {
                        bestc = c2;
                        bestv = s;
                    }
                }
                S[l][i] = bestv;
                setperm(l, i);
                if (bestv != old) {
                    cost = bestc;
                    improved = 1;
                }
            }
        }
    }
    return cost;
}

static const int KF[] = {1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

/* Pick k2 and m with m*k2 >= target, and a random valid r (r = 1 is always valid). */
static int sample_group(long long target, int *oM, int *oK2, int *oR) {
    int nk = (int)(sizeof(KF) / sizeof(KF[0]));
    for (int att = 0; att < 50; att++) {
        int k2 = KF[rint_(nk)];
        long long m = (target + k2 - 1) / k2;
        if (m < 2) m = 2;
        if (m * k2 > GMAX) continue;
        int nc = 0;
        for (long long c = 1; c < m; c++) {
            if (gcd_ll(c, m) != 1) continue;
            if (powmod_ll(c, k2, m) != 1 % m) continue;
            candbuf[nc++] = (int)c;
        }
        if (nc == 0) continue;
        *oM = (int)m;
        *oK2 = k2;
        *oR = candbuf[rint_(nc)];
        return 1;
    }
    return 0;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double tl = atof(argv[4]);
    long long min_n = argc > 5 ? atoll(argv[5]) : 0;

    if (DEG < 1 || DEG > MAXD || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    rs ^= (uint64_t)seed * 0x9E3779B97F4A7C15ULL + 12345ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 4; w++) rnd64();

    double t0 = now_s();
    deadline = t0 + tl;
    int found = 0;
    int bK = 1, bM = 1, bK2 = 1, bR = 1;

    while (now_s() < deadline) {
        int u = rint_(100);
        int k = (u < 50) ? 1 : (u < 85 ? 2 : 3);
        long long g0 = min_n / (2 * k) + 1;
        long long span = g0 / 25 + 6;
        long long target = g0 + rint_((int)span);
        int M = 1, k2 = 1, r = 1;
        if (!sample_group(target, &M, &k2, &r)) continue;
        set_group(M, k2, r);
        K = k;
        NV = 2 * K * G;
        if ((long long)NV <= min_n) continue;

        random_cfg();
        long long raw = breakout(BREAK_ITERS);
        memcpy(GP, P, sizeof(P));
        memcpy(GS, S, sizeof(S));
        long long gbest = raw;

        /* Reheat from the group's best state with a random kick. */
        for (int rt = 0; gbest > 0 && gbest <= REHEAT_MAX && rt < REHEAT_TRIES
                         && now_s() < deadline; rt++) {
            memcpy(P, GP, sizeof(P));
            memcpy(S, GS, sizeof(S));
            int kick = DEG * K / 6 + 1;
            for (int q = 0; q < kick; q++) {
                int l = rint_(DEG), i = rint_(K);
                S[l][i] = rint_(G);
            }
            setall();
            raw = breakout(BREAK_ITERS / 2);
            if (raw < gbest) {
                gbest = raw;
                memcpy(GP, P, sizeof(P));
                memcpy(GS, S, sizeof(S));
            }
        }

        memcpy(P, GP, sizeof(P));
        memcpy(S, GS, sizeof(S));
        setall();
        if (gbest > 0 && gbest <= POLISH_T) polish();
        cost_eval(0);
        if (g_raw == 0) {
            memcpy(RP, P, sizeof(P));
            memcpy(RS, S, sizeof(S));
            bK = K;
            bM = M;
            bK2 = k2;
            bR = r;
            min_n = NV;
            found = 1;
        }
    }

    if (!found) {
        printf("0 0\n");
        return 0;
    }
    set_group(bM, bK2, bR);
    K = bK;
    NV = 2 * K * G;
    memcpy(P, RP, sizeof(P));
    memcpy(S, RS, sizeof(S));
    setall();
    printf("%d %d\n", NV, DEG * K * G);
    for (int l = 0; l < DEG; l++)
        for (int i = 0; i < K; i++)
            for (int g = 0; g < G; g++)
                printf("%d %d\n", i * G + g, (K + P[l][i]) * G + PM[l][i][g]);
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Python glue: exact constructions, then the C search from the best order so far.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
    budget = max(3.0, min(0.85 * time_limit, time_limit - 6.0))
    deadline = start + budget

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

        if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                ap = lib.araujo_lopez_graph(d - 2)
                consider(ap[0], ap[1])
            except Exception:
                pass

    if D >= 4 and time.monotonic() < deadline:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Breakout + reheat search in C, seeded with the best known order as a lower bound.
    if 3 <= d <= 64 and D >= 3:
        c_budget = deadline - time.monotonic() - 1.0
        if c_budget >= 2.0:
            try:
                out = lib.run_c(C_SOURCE, [d, D, seed, f"{c_budget:.2f}", best[0]],
                                timeout=time_limit - 3.0)
                n, e = lib.parse_graph_text(out)
                consider(n, e)
            except Exception:
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
