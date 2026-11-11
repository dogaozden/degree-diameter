"""Bold variant: vertex-transitive bi-Cayley search.

Construction: the bipartite graph on A = G and B = G (G = Z_m semidirect Z_k,
element (a,b) coded as a*k+b), with a_x adjacent to b_{x*s} for each s in a
connection set S of size d. Left multiplication is an automorphism, so the
diameter is at most D iff BFS from a_e and from b_e reaches all 2|G| vertices
within D steps. C searches over (group, S) by annealing the number of unreached
vertices, aiming for |G| above the best known half-order.

Fallbacks: exact PG(2,q) and W(q) incidence graphs, C_{2D} for d = 2, and K_{d,d}.
Every candidate passes lib.is_valid before it is accepted.
"""
import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 8192
#define MAXDEG 32
#define MAXV (2 * MAXN)

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

static double tstart, TL;

static double now(void) {
    return (double)clock() / CLOCKS_PER_SEC - tstart;
}

static int64_t powmod(int64_t b, int64_t e, int64_t m) {
    int64_t r = 1 % m;
    b %= m;
    if (b < 0) b += m;
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

static int DEG, DIAM;

/* group Z_M semidirect Z_K with action r; order GN = GM*GK, element a*GK+b */
static int GM, GK, GN;
static int64_t PW[MAXN];

static void set_group(int M, int K, int r) {
    GM = M;
    GK = K;
    GN = M * K;
    int64_t p = 1 % M;
    for (int t = 0; t < K; t++) {
        PW[t] = p;
        p = p * r % M;
    }
}

/* (a,b)(c,e) = (a + r^b c, b + e) */
static int gmul(int x, int y) {
    int a1 = x / GK, b1 = x % GK;
    int a2 = y / GK, b2 = y % GK;
    int a = (int)((a1 + PW[b1] * (int64_t)a2) % GM);
    int b = (b1 + b2) % GK;
    return a * GK + b;
}

/* inverse of (a,b) is (-r^{-b} a, -b) */
static int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int64_t t = (PW[nb] * (int64_t)a) % GM;
    int a2 = (int)((GM - t) % GM);
    return a2 * GK + nb;
}

static int S[MAXDEG], SI[MAXDEG];
static int nbA[MAXN * MAXDEG];   /* A vertex x -> B index of x*s_i */
static int nbB[MAXN * MAXDEG];   /* B vertex y -> A index of y*s_i^{-1} */
static uint8_t dist[MAXV];
static int que[MAXV];

static void set_s(int i, int s) {
    S[i] = s;
    SI[i] = ginv(s);
    for (int x = 0; x < GN; x++) {
        nbA[x * DEG + i] = GN + gmul(x, s);
        nbB[x * DEG + i] = gmul(x, SI[i]);
    }
}

static int64_t bfs_unreached(int root) {
    int NV = 2 * GN;
    memset(dist, 0xff, (size_t)NV);
    int head = 0, tail = 0, reached = 1;
    dist[root] = 0;
    que[tail++] = root;
    while (head < tail) {
        int v = que[head++];
        int dv = dist[v];
        if (dv >= DIAM) continue;
        if (v < GN) {
            const int *row = nbA + (size_t)v * DEG;
            for (int i = 0; i < DEG; i++) {
                int w = row[i];
                if (dist[w] == 0xff) {
                    dist[w] = (uint8_t)(dv + 1);
                    que[tail++] = w;
                    reached++;
                }
            }
        } else {
            const int *row = nbB + (size_t)(v - GN) * DEG;
            for (int i = 0; i < DEG; i++) {
                int w = row[i];
                if (dist[w] == 0xff) {
                    dist[w] = (uint8_t)(dv + 1);
                    que[tail++] = w;
                    reached++;
                }
            }
        }
    }
    return (int64_t)(NV - reached);
}

/* roots a_e (index 0) and b_e (index GN) cover all pairs by vertex-transitivity on each side */
static int64_t eval_cost(void) {
    return bfs_unreached(0) + bfs_unreached(GN);
}

static int in_S(int s, int cnt) {
    for (int j = 0; j < cnt; j++)
        if (S[j] == s) return 1;
    return 0;
}

static void random_S(void) {
    for (int i = 0; i < DEG; i++) {
        int s;
        do {
            s = rndint(GN);
        } while (in_S(s, i));
        S[i] = s;
    }
    for (int i = 0; i < DEG; i++) set_s(i, S[i]);
}

static int64_t anneal(int iters, double T0, double T1) {
    int64_t cur = eval_cost();
    for (int t = 0; t < iters && cur > 0; t++) {
        if ((t & 63) == 0 && now() > TL) break;
        double T = T0 * pow(T1 / T0, (double)t / (double)iters);
        int i = rndint(DEG);
        int ns;
        do {
            ns = rndint(GN);
        } while (in_S(ns, DEG));
        int old = S[i];
        set_s(i, ns);
        int64_t c = eval_cost();
        if (c <= cur || rnd01() < exp(-(double)(c - cur) / T)) {
            cur = c;
        } else {
            set_s(i, old);
        }
    }
    return cur;
}

/* random group of order N: Z_M semidirect Z_K with K >= 2 and r != 1 when possible, else cyclic */
static void pick_group(int N, int *pM, int *pK, int *pR) {
    int divs[512];
    int nd = 0;
    for (int K = 2; K <= N / 3 && nd < 512; K++)
        if (N % K == 0) divs[nd++] = K;
    for (int att = 0; att < 40 && nd > 0; att++) {
        int K = divs[rndint(nd)];
        int M = N / K;
        int pick = -1, cnt = 0;
        for (int r = 2; r < M; r++) {
            if (gcd64(r, M) != 1) continue;
            if (powmod(r, K, M) != 1 % M) continue;
            cnt++;
            if (rndint(cnt) == 0) pick = r;
        }
        if (pick >= 0) {
            *pM = M;
            *pK = K;
            *pR = pick;
            return;
        }
    }
    *pM = N;
    *pK = 1;
    *pR = 1;
}

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    long long best_total = atoll(argv[3]);
    long long nmax = atoll(argv[4]);
    unsigned long long seed = strtoull(argv[5], NULL, 10);
    TL = atof(argv[6]);
    tstart = (double)clock() / CLOCKS_PER_SEC;

    rs = (seed + 1) * 0x9E3779B97F4A7C15ULL ^ 0xD1B54A32D192ED03ULL;
    if (rs == 0) rs = 1;
    for (int i = 0; i < 8; i++) rnd64();

    if (DEG < 3 || DEG > MAXDEG || DIAM < 3) {
        printf("0 0\n");
        return 0;
    }
    if (nmax > MAXN) nmax = MAXN;
    long long lo = best_total / 2 + 1;   /* need 2N > best_total */
    if (lo < DEG + 1) lo = DEG + 1;

    int found = (int)(lo - 1);
    int have = 0;
    int bestS[MAXDEG];
    int bestN = 0, bestM = 0, bestK = 0, bestR = 0;
    int nearOK = 0, nearN = 0, nearM = 0, nearK = 0, nearR = 0;
    int nearS[MAXDEG];
    int64_t nearCost = 0;
    int fails = 0;
    const int iters = 12000;

    while (now() < TL && found < nmax) {
        int N, M, K, R;
        int warm = nearOK && nearN > found && rnd01() < 0.5;
        if (warm) {
            N = nearN;
            M = nearM;
            K = nearK;
            R = nearR;
        } else {
            int span = 3;
            if (fails < 20) {
                int sp = found / 50;
                if (sp > span) span = sp;
            }
            N = found + 1 + rndint(span);
            if (N > nmax) N = (int)nmax;
            pick_group(N, &M, &K, &R);
        }
        set_group(M, K, R);
        if (warm) {
            for (int i = 0; i < DEG; i++) S[i] = nearS[i];
            int kicks = 1 + rndint(2);
            for (int q = 0; q < kicks; q++) {
                int i = rndint(DEG), s;
                do {
                    s = rndint(GN);
                } while (in_S(s, DEG));
                S[i] = s;
            }
            for (int i = 0; i < DEG; i++) set_s(i, S[i]);
        } else {
            random_S();
        }

        int64_t c = anneal(iters, warm ? 1.0 : 2.0, 0.2);

        if (c == 0) {
            have = 1;
            bestN = N;
            bestM = M;
            bestK = K;
            bestR = R;
            for (int i = 0; i < DEG; i++) bestS[i] = S[i];
            found = N;
            fails = 0;
            nearOK = 0;
        } else {
            fails++;
            if (!nearOK || nearN != N || c < nearCost) {
                nearOK = 1;
                nearN = N;
                nearM = M;
                nearK = K;
                nearR = R;
                nearCost = c;
                for (int i = 0; i < DEG; i++) nearS[i] = S[i];
            }
        }
    }

    if (!have) {
        printf("0 0\n");
        return 0;
    }
    set_group(bestM, bestK, bestR);
    int NB = bestN;
    printf("%d %lld\n", 2 * NB, (long long)NB * DEG);
    for (int x = 0; x < NB; x++)
        for (int i = 0; i < DEG; i++)
            printf("%d %d\n", x, NB + gmul(x, bestS[i]));
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Exact constructions used as fallbacks and calibration returns.
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
    """W(q) for the largest prime power q with q + 1 <= d, restricted to q <= 9 for speed."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


# ----------------------------------------------------------------------------
# Main build: exact fallbacks, then the bi-Cayley C search with the remaining budget.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, valid for every D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # d = 2: cycle of length 2D has diameter D.
    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D >= 4 and time.monotonic() - t0 < 0.15 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if D == 4 and d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # Bold search: vertex-transitive bi-Cayley graphs over semidirect groups, in C.
    if d >= 3 and D >= 3:
        budget = min(0.8 * time_limit, time_limit - 4.0)
        remaining = budget - (time.monotonic() - t0)
        if remaining > 2.0:
            nmax = lib.moore_bound(d, D) // 2
            try:
                text = lib.run_c(
                    C_SOURCE,
                    [d, D, best_n, nmax, int(seed) & 0x7FFFFFFF, round(remaining, 2)],
                    timeout=remaining + 15.0,
                )
                n2, e2 = lib.parse_graph_text(text)
                consider(n2, e2)
            except Exception:
                pass

    return best
