"""Bipartite diameter-D search: exact projective-plane and W(q) constructions in Python,
plus a C-native bi-Cayley annealer over semidirect products Z_m x| Z_k2.

New in this version: the whole search (group sampling, bandit over base sizes, reach-based
cost, annealing, and the threshold that rises after each success) runs in C. Group
multiplication and inverses are computed on the fly, so no G x G tables are needed and very
large groups are cheap. Each success raises the bar for the next trial.
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

typedef unsigned long long u64;
typedef long long ll;

#define MAXD 32
#define MAXK 8
#define PEN 1000LL

static int dd = 0, DD = 0;
static u64 rs = 1;
static clock_t T0;

static u64 rnd64(void) {
    rs ^= rs >> 12;
    rs ^= rs << 25;
    rs ^= rs >> 27;
    return rs * 2685821657736338717ULL;
}
static int rndint(int n) { return (int)(rnd64() % (u64)n); }
static double rnd01(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - T0) / CLOCKS_PER_SEC; }

static int popc(u64 x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod_i(int b, int e, int m) {
    ll r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Group Z_m x| Z_k2, element a*k2+b, (a,b)(c,e) = (a + r^b c, b+e). */
typedef struct { int m, k2, r, G; int pw[64]; } Grp;
static Grp H;

static void set_group(int m, int k2, int r) {
    H.m = m; H.k2 = k2; H.r = r; H.G = m * k2;
    H.pw[0] = 1 % m;
    for (int b = 1; b < k2; b++) H.pw[b] = (int)((ll)H.pw[b - 1] * r % m);
}

static int gmul(int x, int y) {
    int k2 = H.k2, m = H.m;
    int a = x / k2, b = x % k2, c = y / k2, e = y % k2;
    ll t = ((ll)a + (ll)H.pw[b] * c) % m;
    int rb = (b + e) % k2;
    return (int)t * k2 + rb;
}

static int ginv(int s) {
    int k2 = H.k2, m = H.m;
    int c = s / k2, e = s % k2;
    int ne = (k2 - e) % k2;              /* r^{-e} = r^{ne}, and -e = ne mod k2 */
    ll t = (ll)H.pw[ne] * c % m;
    int ca = (int)((m - t) % m);
    return ca * k2 + ne;
}

/* Search state: K base vertices per side, G group order, N = 2KG vertices.
   Layer l maps A-block i to B-block lp[l][i] with voltage S[l][i]. */
static int K, G, N;
static int lp[MAXD][MAXK];
static int S[MAXD][MAXK];
static int *nbr = NULL;          /* nbr[l*N + v] */
static u64 *R = NULL, *Rc = NULL, *Rt = NULL;

static void free_state(void) {
    free(nbr); free(R); free(Rc); free(Rt);
    nbr = NULL; R = NULL; Rc = NULL; Rt = NULL;
}

static void alloc_state(void) {
    free_state();
    N = 2 * K * G;
    nbr = (int *)malloc(sizeof(int) * (size_t)dd * (size_t)N);
    R = (u64 *)malloc(sizeof(u64) * (size_t)N);
    Rc = (u64 *)malloc(sizeof(u64) * (size_t)N);
    Rt = (u64 *)malloc(sizeof(u64) * (size_t)N);
}

static void set_dart(int l, int i) {
    int p = lp[l][i], s = S[l][i];
    int si = ginv(s);
    int *nl = nbr + (size_t)l * N;
    int Ab = i * G, Bb = (K + p) * G;
    for (int g = 0; g < G; g++) {
        nl[Ab + g] = Bb + gmul(g, s);        /* A_{i,g} ~ B_{p, g*s} */
        nl[Bb + g] = Ab + gmul(g, si);       /* B_{p,h} ~ A_{i, h*s^-1} */
    }
}

static void build_all(void) {
    for (int l = 0; l < dd; l++)
        for (int i = 0; i < K; i++)
            set_dart(l, i);
}

/* out[v] bit b set iff dist(v, e_b) <= DD, e_b = identity of block b. */
static void compute_reach(u64 *out) {
    int NN = N;
    for (int v = 0; v < NN; v++) out[v] = 0;
    for (int b = 0; b < 2 * K; b++) out[(size_t)b * G] = 1ULL << b;
    for (int t = 0; t < DD; t++) {
        memcpy(Rt, out, sizeof(u64) * (size_t)NN);
        for (int l = 0; l < dd; l++) {
            const int *nl = nbr + (size_t)l * NN;
            for (int v = 0; v < NN; v++) Rt[v] |= out[nl[v]];
        }
        memcpy(out, Rt, sizeof(u64) * (size_t)NN);
    }
}

static int dup_count(void) {
    int cnt = 0;
    for (int i = 0; i < K; i++)
        for (int a = 0; a < dd; a++)
            for (int b = a + 1; b < dd; b++)
                if (lp[a][i] == lp[b][i] && S[a][i] == S[b][i]) cnt++;
    return cnt;
}

static ll cost_of(const u64 *RR) {
    ll un = 0;
    int tot = 2 * K;
    for (int v = 0; v < N; v++) un += tot - popc(RR[v]);
    return un + PEN * (ll)dup_count();
}

static void random_init(void) {
    for (int l = 0; l < dd; l++) {
        for (int i = 0; i < K; i++) lp[l][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lp[l][i]; lp[l][i] = lp[l][j]; lp[l][j] = t;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(G);
    }
}

/* Simulated annealing. Returns 1 if a valid state (cost 0) was reached. */
static int anneal(long iters, long patience, double t_end) {
    build_all();
    compute_reach(R);
    ll cost = cost_of(R);
    ll best_cost = cost;
    double c0 = cost > 1 ? (double)cost : 1.0;
    long last_imp = 0;
    u64 full = (1ULL << (2 * K)) - 1ULL;

    for (long t = 0; t < iters && cost != 0; t++) {
        if (elapsed() > t_end) break;
        if (t - last_imp > patience) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / (double)iters);
        if (temp < 0.5) temp = 0.5;

        if (K >= 2 && rnd01() < 0.25) {
            /* Layer-swap move: exchange B-targets of two A-blocks in one layer. */
            int l = rndint(dd);
            int i1 = rndint(K);
            int i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int tmp = lp[l][i1]; lp[l][i1] = lp[l][i2]; lp[l][i2] = tmp;
            set_dart(l, i1); set_dart(l, i2);
            compute_reach(Rc);
            ll c2 = cost_of(Rc);
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                memcpy(R, Rc, sizeof(u64) * (size_t)N);
                if (cost < best_cost) { best_cost = cost; last_imp = t; }
            } else {
                tmp = lp[l][i1]; lp[l][i1] = lp[l][i2]; lp[l][i2] = tmp;
                set_dart(l, i1); set_dart(l, i2);
            }
            continue;
        }

        /* Voltage move: defect-targeted with probability 0.4, otherwise uniform. */
        int l = -1, i = -1;
        if (rnd01() < 0.4) {
            int nb = 0;
            for (int v = 0; v < N; v++) if (R[v] != full) nb++;
            if (nb > 0) {
                int pick = rndint(nb), u = -1;
                for (int v = 0; v < N; v++) {
                    if (R[v] != full) {
                        if (pick == 0) { u = v; break; }
                        pick--;
                    }
                }
                int block = u / G;
                l = rndint(dd);
                if (block < K) {
                    i = block;
                } else {
                    int p = block - K;
                    for (int j = 0; j < K; j++) if (lp[l][j] == p) { i = j; break; }
                }
            }
        }
        if (i < 0) { l = rndint(dd); i = rndint(K); }

        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        compute_reach(Rc);
        ll c2 = cost_of(Rc);
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            memcpy(R, Rc, sizeof(u64) * (size_t)N);
            if (cost < best_cost) { best_cost = cost; last_imp = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

static const int K2S[20] = {1, 1, 2, 2, 3, 4, 5, 6, 7, 8, 9, 10, 12, 14, 16, 18, 20, 24, 30, 36};

int main(int argc, char **argv) {
    int ch;
    while ((ch = getchar()) != EOF) { }
    if (argc < 6) { printf("0 0\n"); return 0; }
    dd = atoi(argv[1]);
    DD = atoi(argv[2]);
    u64 seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    int best_n = atoi(argv[5]);
    if (dd < 1 || dd > MAXD || DD < 2 || budget <= 0) { printf("0 0\n"); return 0; }

    rs = seed * 0x9E3779B97F4A7C15ULL + 0x2545F4914F6CDD1DULL;
    if (rs == 0) rs = 88172645463325252ULL;
    for (int w = 0; w < 16; w++) rnd64();
    T0 = clock();

    int bn = best_n;
    int have = 0;
    int bK = 0, bm = 0, bk2 = 0, br = 0;
    int blp[MAXD][MAXK], bS[MAXD][MAXK];
    long trials[MAXK + 1], wins[MAXK + 1];
    for (int k = 0; k <= MAXK; k++) { trials[k] = 0; wins[k] = 0; }

    while (elapsed() < budget) {
        int k;
        if (rnd01() < 0.2) {
            k = 1 + rndint(4);
        } else {
            double bestsc = -1.0;
            k = 1;
            for (int kk = 1; kk <= 4; kk++) {
                double sc = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                if (sc > bestsc) { bestsc = sc; k = kk; }
            }
        }
        int base = bn / (2 * k);
        int target = base + 1 + rndint(base / 8 + 2);
        if (target < 2) target = 2;
        int k2 = K2S[rndint(20)];
        int m = (target + k2 - 1) / k2;   /* G = m*k2 >= target > bn/(2k) */
        if (m < 2) m = 2;
        int r = 1;
        if (k2 == 2 && m > 2 && rnd01() < 0.3) {
            int cand = m - 1;             /* dihedral-type action */
            if (gcd_i(cand, m) == 1 && ((ll)cand * cand) % m == 1 % m) r = cand;
        } else if (k2 > 1 && m > 2) {
            for (int tr = 0; tr < 60; tr++) {
                int c = 2 + rndint(m - 2);
                if (gcd_i(c, m) == 1 && powmod_i(c, k2, m) == 1 % m) { r = c; break; }
            }
        }
        set_group(m, k2, r);
        K = k;
        G = H.G;
        if (2 * K * G <= bn) continue;

        trials[k]++;
        alloc_state();
        random_init();
        int ok = anneal(30000, 4000, budget);
        if (ok) {
            wins[k]++;
            bn = 2 * K * G;
            have = 1;
            bK = K; bm = m; bk2 = k2; br = r;
            memcpy(blp, lp, sizeof(lp));
            memcpy(bS, S, sizeof(S));
        }
    }

    if (have) {
        set_group(bm, bk2, br);
        K = bK;
        G = H.G;
        alloc_state();
        memcpy(lp, blp, sizeof(lp));
        memcpy(S, bS, sizeof(S));
        build_all();
        printf("%d %d\n", N, dd * K * G);
        for (int u = 0; u < K * G; u++)
            for (int l = 0; l < dd; l++)
                printf("%d %d\n", u, nbr[(size_t)l * N + u]);
    } else {
        printf("0 0\n");
    }
    free_state();
    return 0;
}
"""


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


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2, so it is valid for D >= 2.
    best = lib.haar_graph(d, range(d))
    best_n = best[0]

    def consider(n, e):
        nonlocal best, best_n
        if n > best_n and lib.is_valid(n, e, d, D):
            best = (n, e)
            best_n = n

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best

    if D == 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    # C-native bi-Cayley search over semidirect groups; it starts from the best
    # order found so far and only accepts strictly larger graphs.
    elapsed = time.monotonic() - t0
    budget = min(0.9 * time_limit, time_limit - elapsed - 8.0)
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{budget:.3f}", best_n],
                            stdin_graph=None, timeout=budget + 4.0)
            n, edges = lib.parse_graph_text(out)
            consider(n, edges)
        except (RuntimeError, ValueError):
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
