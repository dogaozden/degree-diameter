import itertools
import time

import lib

C_SOURCE = r'''
/* Bipartite degree-diameter search core (bi-Cayley lifts + validation).
 *
 * Usage:   prog d D seed time_limit   < start_graph
 * stdin:   "n m" then m lines "u v" (a start graph, or "0 0"). It is kept only if valid.
 * stdout:  "n m" then m lines "u v": the largest valid graph found.
 *
 * Search: bi-Cayley lifts over Z_m x| Z_k2 (order G) with k base vertices per side.
 * Layer l pairs A-block i with B-block lay[l][i] through voltage S[l][i], so every
 * vertex has degree d. Simulated annealing on the voltages and layer permutations
 * minimises unreached (block-representative, vertex) pairs plus duplicate-dart penalty.
 * Each success is fully re-validated before it is accepted.
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXN 8192
#define MAXD 16
#define MAXK 4
#define MAXW (MAXN / 64)
#define MAXE (MAXN * MAXD / 2)
#define PEN 1000
#define ITERS 6000
#define PATIENCE 1500

static int d, D;
static double t_end;
static uint64_t rs = 88172645463325252ULL;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}

static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 100000000L) break;
    }
    return 2 * s;
}

/* ------------------------------------------------------------ best graph store */

static int best_n = 0, best_m = 0;
static int best_u[MAXE], best_v[MAXE];
static int eu[MAXE], ev[MAXE];

static void store_best(int n, int m, const int *u, const int *v) {
    best_n = n;
    best_m = m;
    memcpy(best_u, u, sizeof(int) * (size_t)m);
    memcpy(best_v, v, sizeof(int) * (size_t)m);
}

/* ------------------------------------------------------------ full validation */

static int vadj[MAXN][MAXD];
static int vdeg[MAXN];
static int vcol[MAXN];
static int vq[MAXN];
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];

static int valid_edges(int n, int m, const int *u_, const int *v_) {
    if (n <= 0 || n > MAXN || m < 0 || m > MAXE) return 0;
    if (n == 1) return m == 0;
    for (int v = 0; v < n; v++) vdeg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = u_[e], v = v_[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (vdeg[u] >= d || vdeg[v] >= d) return 0;
        vadj[u][vdeg[u]++] = v;
        vadj[v][vdeg[v]++] = u;
    }
    for (int v = 0; v < n; v++)
        for (int i = 0; i < vdeg[v]; i++)
            for (int j = 0; j < i; j++)
                if (vadj[v][i] == vadj[v][j]) return 0;
    /* bipartite */
    for (int v = 0; v < n; v++) vcol[v] = -1;
    for (int s = 0; s < n; s++) {
        if (vcol[s] != -1) continue;
        int h = 0, t = 0;
        vcol[s] = 0;
        vq[t++] = s;
        while (h < t) {
            int x = vq[h++];
            for (int i = 0; i < vdeg[x]; i++) {
                int y = vadj[x][i];
                if (vcol[y] == -1) {
                    vcol[y] = 1 - vcol[x];
                    vq[t++] = y;
                } else if (vcol[y] == vcol[x]) {
                    return 0;
                }
            }
        }
    }
    /* diameter <= D via bitsets */
    int W = (n + 63) / 64;
    uint64_t *cur = BA, *nxt = BB;
    memset(cur, 0, sizeof(uint64_t) * (size_t)n * (size_t)W);
    for (int v = 0; v < n; v++) cur[(size_t)v * W + v / 64] |= 1ULL << (v % 64);
    for (int r = 0; r < D; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + (size_t)v * W;
            const uint64_t *src = cur + (size_t)v * W;
            memcpy(dst, src, sizeof(uint64_t) * (size_t)W);
            for (int i = 0; i < vdeg[v]; i++) {
                const uint64_t *s = cur + (size_t)vadj[v][i] * W;
                for (int w = 0; w < W; w++) dst[w] |= s[w];
            }
        }
        uint64_t *t = cur;
        cur = nxt;
        nxt = t;
    }
    for (int v = 0; v < n; v++) {
        int c = 0;
        const uint64_t *s = cur + (size_t)v * W;
        for (int w = 0; w < W; w++) c += __builtin_popcountll(s[w]);
        if (c != n) return 0;
    }
    return 1;
}

/* ------------------------------------------------------------ bi-Cayley lift state */

static int ck;          /* base vertices per side */
static int ck2;         /* k2 of Z_m x| Z_k2 */
static int cm;          /* m */
static int cG;          /* group order m*k2 */
static int cN;          /* number of vertices 2*ck*cG */
static int rp[32];      /* rp[b] = r^b mod m */
static int lay[MAXD][MAXK];
static int S[MAXD][MAXK];
static int nbr[MAXD][MAXN];
static uint64_t RES[MAXN];

static int gmul(int x, int y) {
    int a = x / ck2, b = x % ck2, c = y / ck2, e = y % ck2;
    long t = ((long)a + (long)rp[b] * c) % cm;
    return (int)(t * ck2 + (b + e) % ck2);
}

/* Write layer l's edges for A-block i (voltage S[l][i]) into nbr. */
static void set_dart(int l, int i) {
    int j = lay[l][i], s = S[l][i];
    int A0 = i * cG, B0 = (ck + j) * cG;
    for (int g = 0; g < cG; g++) {
        int t = gmul(g, s);
        nbr[l][A0 + g] = B0 + t;
        nbr[l][B0 + t] = A0 + g;
    }
}

static int dupcount(void) {
    int cnt = 0;
    for (int l = 0; l < d; l++)
        for (int i = 0; i < ck; i++)
            for (int l2 = 0; l2 < l; l2++)
                if (S[l2][i] == S[l][i] && lay[l2][i] == lay[l][i]) cnt++;
    return cnt;
}

/* Cost: unreached (block representative, vertex) pairs + PEN * duplicate darts.
 * Left multiplication is an automorphism, so block representatives suffice. */
static long eval_cost(void) {
    static uint64_t X1[MAXN], X2[MAXN];
    int N = cN, G = cG, k = ck;
    uint64_t *cur = X1, *nxt = X2;
    for (int v = 0; v < N; v++) cur[v] = 0;
    for (int b = 0; b < 2 * k; b++) cur[(long)b * G] = 1ULL << b;
    for (int r = 0; r < D; r++) {
        int changed = 0;
        for (int v = 0; v < N; v++) {
            uint64_t x = cur[v];
            for (int l = 0; l < d; l++) x |= cur[nbr[l][v]];
            nxt[v] = x;
            changed |= (x != cur[v]);
        }
        uint64_t *tmp = cur;
        cur = nxt;
        nxt = tmp;
        if (!changed) break;
    }
    long cost = 0;
    for (int v = 0; v < N; v++) {
        RES[v] = cur[v];
        cost += 2 * k - __builtin_popcountll(cur[v]);
    }
    cost += (long)PEN * dupcount();
    return cost;
}

static void random_init(void) {
    for (int l = 0; l < d; l++) {
        for (int i = 0; i < ck; i++) lay[l][i] = i;
        for (int i = ck - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = lay[l][i];
            lay[l][i] = lay[l][j];
            lay[l][j] = t;
        }
        for (int i = 0; i < ck; i++) {
            S[l][i] = rndint(cG);
            set_dart(l, i);
        }
    }
}

/* Random group Z_m x| Z_k2 with m*k2 >= target, r^k2 = 1 mod m, gcd(r, m) = 1. */
static const int K2C[] = {1, 2, 2, 3, 3, 4, 4, 5, 6, 8, 9, 10, 12};

static void sample_group(long target) {
    int k2 = K2C[rndint(13)];
    long m = (target + k2 - 1) / k2;
    if (m < 2) m = 2;
    long r = 1;
    if (k2 > 1 && m > 2) {
        int found = 0;
        if (k2 == 2 && rnd01() < 0.3) {
            long c = m - 1;
            if (gcd_i((int)c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                found = 1;
            }
        }
        for (int tr = 0; !found && tr < 60; tr++) {
            long c = 2 + rndint((int)(m - 2));
            if (gcd_i((int)c, (int)m) == 1 && powmod(c, k2, m) == 1 % m) {
                r = c;
                found = 1;
            }
        }
    }
    cm = (int)m;
    ck2 = k2;
    cG = (int)(m * k2);
    rp[0] = 1 % cm;
    for (int b = 1; b < k2; b++) rp[b] = (int)((long)rp[b - 1] * r % cm);
}

/* SA over voltages and layer permutations. Returns 1 when cost reaches 0. */
static int sa_run(double deadline) {
    int k = ck, G = cG, N = cN;
    uint64_t full = (1ULL << (2 * k)) - 1;
    random_init();
    long cost = eval_cost();
    double c0 = cost > 0 ? (double)cost : 1.0;
    long bestc = cost, last = 0;
    for (long t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 63) == 0 && now() > deadline) break;
        if (t - last > PATIENCE) break;
        double temp = 0.01 * c0 * (1.0 - (double)t / ITERS);
        if (temp < 0.5) temp = 0.5;

        if (k >= 2 && rnd01() < 0.25) {
            int l = rndint(d);
            int i1 = rndint(k), i2 = rndint(k - 1);
            if (i2 >= i1) i2++;
            int tt = lay[l][i1];
            lay[l][i1] = lay[l][i2];
            lay[l][i2] = tt;
            set_dart(l, i1);
            set_dart(l, i2);
            long c2 = eval_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost < bestc) { bestc = cost; last = t; }
            } else {
                tt = lay[l][i1];
                lay[l][i1] = lay[l][i2];
                lay[l][i2] = tt;
                set_dart(l, i1);
                set_dart(l, i2);
            }
            continue;
        }

        /* voltage move, defect-targeted with probability 0.4 */
        int target = -1;
        if (rnd01() < 0.4) {
            for (int tr = 0; tr < 30; tr++) {
                int v = rndint(N);
                if (RES[v] != full) { target = v; break; }
            }
        }
        int l, i;
        if (target >= 0) {
            int block = target / G;
            l = rndint(d);
            if (block < k) {
                i = block;
            } else {
                int j = block - k;
                i = -1;
                for (int ii = 0; ii < k; ii++)
                    if (lay[l][ii] == j) { i = ii; break; }
                if (i < 0) continue;
            }
        } else {
            l = rndint(d);
            i = rndint(k);
        }
        int old = S[l][i];
        int nw = rndint(G);
        if (nw == old) continue;
        S[l][i] = nw;
        set_dart(l, i);
        long c2 = eval_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
            cost = c2;
            if (cost < bestc) { bestc = cost; last = t; }
        } else {
            S[l][i] = old;
            set_dart(l, i);
        }
    }
    return cost == 0;
}

/* Turn the current zero-cost lift into an edge list and keep it if valid and larger. */
static int record_lift(void) {
    int k = ck, G = cG, N = cN;
    if (N <= best_n) return 0;
    int m = 0;
    for (int l = 0; l < d; l++)
        for (int x = 0; x < k * G; x++) {
            eu[m] = x;
            ev[m] = nbr[l][x];
            m++;
        }
    if (!valid_edges(N, m, eu, ev)) return 0;
    store_best(N, m, eu, ev);
    return 1;
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit < start_graph\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.93 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 1 || d > MAXD || D < 1) {
        printf("1 0\n");
        return 0;
    }

    /* optional start graph */
    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) == 2 && n0 > 0 && n0 <= MAXN && m0 >= 0 && m0 <= MAXE) {
        int ok = 1;
        for (int e = 0; e < m0 && ok; e++)
            if (scanf("%d %d", &eu[e], &ev[e]) != 2) ok = 0;
        if (ok && valid_edges(n0, m0, eu, ev)) store_best(n0, m0, eu, ev);
    }

    /* fallback: K_{d,d}, valid for D >= 2 */
    if (best_n == 0) {
        best_n = 2 * d;
        best_m = 0;
        for (int a = 0; a < d; a++)
            for (int b = 0; b < d; b++) {
                best_u[best_m] = a;
                best_v[best_m] = d + b;
                best_m++;
            }
    }

    if (D >= 2 && d >= 2) {
        long trials[MAXK + 1] = {0}, wins[MAXK + 1] = {0};
        long mb = moore_bound();
        while (now() < t_end) {
            int k;
            if (rnd01() < 0.2) {
                k = 1 + rndint(MAXK);
            } else {
                double bv = -1.0;
                k = 1;
                for (int kk = 1; kk <= MAXK; kk++) {
                    double v = (wins[kk] + 1.0) / (trials[kk] + 2.0) + 0.02 * rnd01();
                    if (v > bv) { bv = v; k = kk; }
                }
            }
            long base = best_n / (2 * k);
            long target = base + 1 + rndint((int)(base / 8 + 2));
            sample_group(target);
            ck = k;
            cN = 2 * k * cG;
            if (cN > MAXN || cN > mb || cN <= best_n) continue;
            trials[k]++;
            if (sa_run(t_end)) {
                if (record_lift()) wins[k]++;
            }
        }
    }

    printf("%d %d\n", best_n, best_m);
    for (int e = 0; e < best_m; e++) printf("%d %d\n", best_u[e], best_v[e]);
    return 0;
}
'''


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
    """W(q) for the largest prime power q <= min(d - 1, 9)."""
    for q in range(min(d - 1, 9), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def _known_start(d, D):
    """Return (graph or None, exact). exact means the graph is optimal and needs no search."""
    if D == 3 and lib.is_prime_power(d - 1):
        return lib.projective_plane_incidence(d - 1), True
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        return lib.araujo_lopez_graph(d - 2), False
    if D == 4:
        return _best_gq(d), False
    return None, False


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    best = lib.haar_graph(d, range(d))   # K_{d,d}: valid for D >= 2
    if d < 3 or D < 2:
        return best

    try:
        start, exact = _known_start(d, D)
    except Exception:
        start, exact = None, False
    if start is not None and start[0] > best[0] and lib.is_valid(start[0], start[1], d, D):
        best = start
        if exact:
            return best

    budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
    if budget < 1.0:
        return best
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2)],
                         stdin_graph=best, timeout=budget + 10)
        out = lib.parse_graph_text(text)
        if out[0] > best[0] and lib.is_valid(out[0], out[1], d, D):
            best = out
    except Exception:
        pass
    return best
