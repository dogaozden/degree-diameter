import random
import time

import lib


# ----------------------------------------------------------------------------
# C engine: annealing over bipartite voltage lifts of Z_m x| Z_k2.
#
# A candidate is k black base vertices A_i and k white base vertices B_j, with
# d layers. Layer l has a permutation sig[l] and voltages vol[l][i]. The lift
# has vertices (i, g) and (j, h) for g, h in the group, and edges
# (i, g) -- (sig[l][i], g * vol[l][i]). Left multiplication is an automorphism,
# so distances only need to be computed from the 2k block representatives.
# Each evaluation is therefore 2k BFS runs of depth D, with no bitsets. The cost
# is the number of unreached (block, vertex) pairs plus a penalty per duplicate
# dart. Cost zero means a valid graph with 2*k*|G| vertices.
# ----------------------------------------------------------------------------

LIFT_C = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

typedef uint64_t u64;
#define MAXN 8192
#define MAXD 16
#define MAXK 4
#define PEN 1000

static u64 rs = 88172645463325252ULL;
static u64 rnd(void) { rs ^= rs << 13; rs ^= rs >> 7; rs ^= rs << 17; return rs; }
static int rint_(int n) { return (int)(rnd() % (u64)n); }
static double rdbl(void) { return (double)(rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int d_, D_, k_, G_, m_, k2_, N_;
static int sig[MAXD][MAXK], vol[MAXD][MAXK], rev_[MAXD][MAXK];
static int rp[64];
static int *nbr, *vis, *dist_, *qb;
static int stamp_ = 0;
static double tend_;

/* Semidirect product Z_m x| Z_k2, element a*k2+b, (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1+b2). */
static int mulg(int x, int y) {
    int a1 = x / k2_, b1 = x % k2_, a2 = y / k2_, b2 = y % k2_;
    return ((a1 + rp[b1] * a2) % m_) * k2_ + (b1 + b2) % k2_;
}
static int invg(int s) {
    int a = s / k2_, b = s % k2_;
    int nb = (k2_ - b) % k2_;
    int na = (m_ - (rp[nb] * a) % m_) % m_;
    return na * k2_ + nb;
}

static long long pw(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}
static int gcd_(int a, int b) { while (b) { int t = a % b; a = b; b = t; } return a; }

static int setup_group(int Gt) {
    static const int K2[] = {1,1,1,2,2,2,3,3,4,4,5,6,6,7,8,8,9,10,12,14,16,18,20,24};
    int k2 = K2[rint_((int)(sizeof K2 / sizeof K2[0]))];
    int m = (Gt + k2 - 1) / k2 + rint_(3);
    if (m < 2) m = 2;
    int r = 1;
    if (k2 > 1) {
        int ok = 0;
        for (int t = 0; t < 400 && !ok; t++) {
            int c = 1 + rint_(m - 1);
            if (gcd_(c, m) == 1 && pw(c, k2, m) == 1 % m) { r = c; ok = 1; }
        }
        if (!ok) return 0;
    }
    m_ = m;
    k2_ = k2;
    G_ = m * k2;
    rp[0] = 1 % m;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long long)rp[b - 1] * r % m);
    return 1;
}

static void rebuild_rev(int l) {
    for (int i = 0; i < k_; i++) rev_[l][sig[l][i]] = i;
}

static void build_nbr(void) {
    int k = k_, G = G_, d = d_;
    for (int i = 0; i < k; i++)
        for (int g = 0; g < G; g++) {
            int v = i * G + g;
            for (int l = 0; l < d; l++)
                nbr[v * d + l] = (k + sig[l][i]) * G + mulg(g, vol[l][i]);
        }
    for (int j = 0; j < k; j++)
        for (int h = 0; h < G; h++) {
            int v = (k + j) * G + h;
            for (int l = 0; l < d; l++) {
                int i = rev_[l][j];
                nbr[v * d + l] = i * G + mulg(h, invg(vol[l][i]));
            }
        }
}

static long long eval_cost(void) {
    int k = k_, G = G_, d = d_, N = N_;
    build_nbr();
    long long unreached = 0;
    for (int s = 0; s < 2 * k; s++) {
        int src = s * G;
        stamp_++;
        int head = 0, tail = 0;
        qb[tail++] = src;
        vis[src] = stamp_;
        dist_[src] = 0;
        while (head < tail) {
            int v = qb[head++];
            if (dist_[v] >= D_) continue;
            int dv = dist_[v] + 1;
            for (int l = 0; l < d; l++) {
                int u = nbr[v * d + l];
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    dist_[u] = dv;
                    qb[tail++] = u;
                }
            }
        }
        unreached += N - tail;
    }
    int dup = 0;
    for (int i = 0; i < k; i++)
        for (int l = 0; l < d; l++)
            for (int l2 = l + 1; l2 < d; l2++)
                if (sig[l][i] == sig[l2][i] && vol[l][i] == vol[l2][i]) dup++;
    return unreached + (long long)PEN * dup;
}

static long long anneal(int iters) {
    long long cost = eval_cost();
    if (cost == 0) return 0;
    double T0 = 1.0 + 0.05 * (double)cost;
    const double T1 = 0.2;
    int k = k_, d = d_;
    for (int t = 0; t < iters && cost > 0; t++) {
        if ((t & 63) == 0 && (double)clock() >= tend_) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int l = rint_(d), i = rint_(k);
        if (k >= 2 && rdbl() < 0.2) {
            int i2 = rint_(k - 1);
            if (i2 >= i) i2++;
            int tmp = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = tmp;
            rebuild_rev(l);
            long long c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                tmp = sig[l][i]; sig[l][i] = sig[l][i2]; sig[l][i2] = tmp;
                rebuild_rev(l);
            }
        } else {
            int old = vol[l][i];
            int nw = rint_(G_ - 1);
            if (nw >= old) nw++;
            vol[l][i] = nw;
            long long c2 = eval_cost();
            if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) cost = c2;
            else vol[l][i] = old;
        }
    }
    return cost;
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    d_ = atoi(argv[1]);
    D_ = atoi(argv[2]);
    rs ^= (u64)strtoull(argv[3], NULL, 10) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    double lim = atof(argv[4]);
    int minN = argc > 5 ? atoi(argv[5]) : 0;
    if (d_ < 2 || d_ > MAXD || D_ < 1) {
        printf("0 0\n");
        return 0;
    }
    nbr = malloc(sizeof(int) * (size_t)MAXN * MAXD);
    vis = calloc(MAXN, sizeof(int));
    dist_ = malloc(sizeof(int) * MAXN);
    qb = malloc(sizeof(int) * MAXN);
    int *bestE = malloc(sizeof(int) * (size_t)MAXN * MAXD);
    if (!nbr || !vis || !dist_ || !qb || !bestE) {
        printf("0 0\n");
        return 0;
    }
    int bestN = minN, bestM = 0;
    clock_t c0 = clock();
    tend_ = (double)c0 + lim * CLOCKS_PER_SEC;

    while ((double)clock() < tend_) {
        int k = 1 + rint_(MAXK);
        int Gt = bestN / (2 * k) + 1 + rint_(3);
        if (!setup_group(Gt)) continue;
        if (2 * k * G_ > MAXN) continue;
        k_ = k;
        N_ = 2 * k * G_;
        for (int l = 0; l < d_; l++) {
            for (int i = 0; i < k; i++) sig[l][i] = i;
            for (int i = k - 1; i > 0; i--) {
                int j = rint_(i + 1);
                int t = sig[l][i]; sig[l][i] = sig[l][j]; sig[l][j] = t;
            }
            rebuild_rev(l);
            for (int i = 0; i < k; i++) vol[l][i] = rint_(G_);
        }
        long long c = anneal(6000);
        if (c == 0 && N_ > bestN) {
            build_nbr();
            int M = 0;
            for (int i = 0; i < k_; i++)
                for (int g = 0; g < G_; g++) {
                    int v = i * G_ + g;
                    for (int l = 0; l < d_; l++) {
                        bestE[2 * M] = v;
                        bestE[2 * M + 1] = nbr[v * d_ + l];
                        M++;
                    }
                }
            bestM = M;
            bestN = N_;
        }
    }
    if (bestM == 0) {
        printf("0 0\n");
        return 0;
    }
    printf("%d %d\n", bestN, bestM);
    for (int e = 0; e < bestM; e++) printf("%d %d\n", bestE[2 * e], bestE[2 * e + 1]);
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Python constructions and glue.
# ----------------------------------------------------------------------------

def _best_pg(d):
    """Incidence graph of PG(2, q) for the largest prime power q with q + 1 <= d."""
    for q in range(d - 1, 1, -1):
        if lib.is_prime_power(q):
            return lib.projective_plane_incidence(q)
    return None


def _bipartition(n, adj):
    """2-colouring of the graph, or None if it is not bipartite."""
    color = [-1] * n
    for s in range(n):
        if color[s] != -1:
            continue
        color[s] = 0
        stack = [s]
        while stack:
            u = stack.pop()
            for v in adj[u]:
                if color[v] == -1:
                    color[v] = 1 - color[u]
                    stack.append(v)
                elif color[v] == color[u]:
                    return None
    return color


def _slack_extend(n, edges, d, D, rng, deadline):
    """Greedily add vertices using spare degree; returns a valid (n, edges)."""
    edges = [tuple(e) for e in edges]
    adj = lib.adjacency(n, edges)
    color = _bipartition(n, adj)
    if color is None:
        return n, edges
    deg = [len(a) for a in adj]
    grew = True
    while grew and time.monotonic() < deadline:
        grew = False
        for side in (0, 1):
            spare = [v for v in range(n) if color[v] == side and deg[v] < d]
            if len(spare) < d:
                continue
            for _ in range(30):
                if time.monotonic() > deadline or len(spare) < d:
                    break
                pick = rng.sample(spare, d)
                cand = edges + [(v, n) for v in pick]
                if lib.is_valid(n + 1, cand, d, D):
                    edges = cand
                    n += 1
                    color.append(1 - side)
                    deg.append(d)
                    for v in pick:
                        deg[v] += 1
                    spare = [v for v in spare if deg[v] < d]
                    grew = True
                    break
    return n, edges


def _lift_in_c(d, D, seconds, seed, min_n):
    """Run the C voltage-lift annealer; returns parsed (n, edges), possibly (0, [])."""
    out = lib.run_c(LIFT_C, [d, D, seed, f"{seconds:.2f}", min_n],
                    stdin_graph=None, timeout=seconds + 20.0)
    return lib.parse_graph_text(out)


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    rng = random.Random(seed)

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    best = lib.haar_graph(d, range(d))  # K_{d,d}, valid for D >= 2

    def consider(n, e):
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact construction for D = 3 (calibration case): return immediately.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    # Main search: C annealing over bipartite voltage lifts of semidirect products.
    if 2 <= d <= 16:
        lift_budget = max(1.0, min(time_limit - 12.0, 0.8 * time_limit))
        try:
            ln, le = _lift_in_c(d, D, lift_budget, rng.randrange(1, 1 << 30), best[0])
            consider(ln, le)
        except Exception:
            pass  # keep the valid fallback

    # Use spare degree on whatever was found, within the remaining time.
    slack_end = t0 + time_limit - 8.0
    if time.monotonic() < slack_end - 1.0:
        try:
            n2, e2 = _slack_extend(best[0], best[1], d, D, rng, slack_end)
            consider(n2, e2)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
