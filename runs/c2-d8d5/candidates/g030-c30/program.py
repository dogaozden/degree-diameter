"""Bold variant: exact constructions first, then a C engine that anneals exact bi-Cayley lifts
over semidirect products Z_m x| Z_t with a larger base size k (k up to 12). Validity is checked
exactly by BFS from the 2k block representatives, since the lift is invariant under left
multiplication by the group."""
import itertools
import time

import lib


# ----------------------------------------------------------------------------
# Exact and small constructions (calibration cases return immediately).
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
# C engine: simulated annealing over bi-Cayley lifts Z_m x| Z_t with base size k.
# Layers are d perfect matchings between A_0..A_{k-1} and B_0..B_{k-1}, each with a
# voltage. Vertex A_{i,g} ~ B_{pi_l(i), g*s_{l,i}}. Left multiplication is an
# automorphism, so checking BFS from the 2k identity representatives is exact.
# ----------------------------------------------------------------------------

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 1100
#define MAXK 12
#define MAXD 32
#define MAXV (2 * MAXK * MAXG)
#define PEN 200L

static int d, D;
static double t_end;

static double now(void) {
    struct timespec ts;
    clock_gettime(CLOCK_MONOTONIC, &ts);
    return ts.tv_sec + ts.tv_nsec * 1e-9;
}

static uint64_t rs = 88172645463325252ULL;
static uint64_t rnd(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rndint(int k) { return (int)(rnd() % (uint64_t)k); }
static double rnd01(void) { return (rnd() >> 11) * (1.0 / 9007199254740992.0); }

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

static int gcd(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static long moore_bound(void) {
    if (D <= 0 || d <= 0) return 1;
    if (d == 1) return 2;
    if (d == 2) return 2L * D;
    long s = 0, p = 1;
    for (int i = 0; i < D; i++) {
        s += p;
        p *= (d - 1);
        if (s > 1000000000L) break;
    }
    return 2 * s;
}

/* Group Z_gm x| Z_gt, element a*gt+b, (a,b)(c,e) = (a + r^b c mod gm, b+e mod gt). */
static int gm, gt, gN;
static int rp[MAXG];
static uint16_t MT[MAXG][MAXG];
static int INV[MAXG];

static int mul_el(int x, int y) {
    int a = x / gt, b = x % gt, c = y / gt, e = y % gt;
    return (int)(((long)a + (long)rp[b] * c) % gm) * gt + (b + e) % gt;
}

static void set_group(int m, int t, int r) {
    gm = m;
    gt = t;
    gN = m * t;
    rp[0] = 1 % m;
    for (int b = 1; b < t; b++) rp[b] = (int)((long)rp[b - 1] * r % m);
    for (int x = 0; x < gN; x++)
        for (int y = 0; y < gN; y++)
            MT[x][y] = (uint16_t)mul_el(x, y);
    for (int s = 0; s < gN; s++)
        for (int y = 0; y < gN; y++)
            if (MT[s][y] == 0) { INV[s] = y; break; }
}

/* Uniform over non-abelian options with probability 0.85, else a random abelian Z_m x Z_t. */
static int pick_group(int N, int *om, int *ot, int *orr) {
    long cnt = 0;
    int bm = N, bt = 1, br = 1;
    for (int t = 2; t <= N; t++) {
        if (N % t) continue;
        int m = N / t;
        if (m < 2) continue;
        for (int r = 2; r < m; r++) {
            if (gcd(r, m) != 1) continue;
            if (powmod(r, t, m) != 1 % m) continue;
            cnt++;
            if (rndint((int)(cnt > 2000000000L ? 2000000000L : cnt)) == 0) {
                bm = m; bt = t; br = r;
            }
        }
    }
    if (cnt > 0 && rnd01() < 0.85) {
        *om = bm; *ot = bt; *orr = br;
        return 1;
    }
    int divs[256], nd = 0;
    for (int t = 1; t <= N && nd < 256; t++)
        if (N % t == 0) divs[nd++] = t;
    int t = divs[rndint(nd)];
    int m = N / t;
    *om = m;
    *ot = t;
    *orr = 1 % m;
    return 1;
}

static int K;
static int pi_[MAXD][MAXK], ipi[MAXD][MAXK], S[MAXD][MAXK];

static void random_state(void) {
    for (int l = 0; l < d; l++) {
        int perm[MAXK];
        for (int i = 0; i < K; i++) perm[i] = i;
        for (int i = K - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int t = perm[i]; perm[i] = perm[j]; perm[j] = t;
        }
        for (int i = 0; i < K; i++) {
            pi_[l][i] = perm[i];
            ipi[l][perm[i]] = i;
        }
        for (int i = 0; i < K; i++) S[l][i] = rndint(gN);
    }
}

/* Neighbours of vertex v (A block first, then B block). Returns d. */
static int nbr(int v, int *out) {
    int kN = K * gN;
    if (v < kN) {
        int i = v / gN, g = v - i * gN;
        for (int l = 0; l < d; l++)
            out[l] = kN + pi_[l][i] * gN + (int)MT[g][S[l][i]];
    } else {
        int u = v - kN, j = u / gN, h = u - j * gN;
        for (int l = 0; l < d; l++) {
            int i = ipi[l][j];
            out[l] = i * gN + (int)MT[h][INV[S[l][i]]];
        }
    }
    return d;
}

static int vis[MAXV];
static int vstamp = 0;
static int qb[MAXV];

/* Number of vertices NOT within distance D of src. */
static int bfs_unreached(int src) {
    int V = 2 * K * gN;
    int nb[MAXD];
    vstamp++;
    int head = 0, tail = 0;
    qb[tail++] = src;
    vis[src] = vstamp;
    for (int depth = 0; depth < D && head < tail; depth++) {
        int end = tail;
        while (head < end) {
            int v = qb[head++];
            nbr(v, nb);
            for (int t = 0; t < d; t++) {
                int w = nb[t];
                if (vis[w] != vstamp) {
                    vis[w] = vstamp;
                    qb[tail++] = w;
                }
            }
        }
    }
    return V - tail;
}

static int dupcount(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int l1 = 0; l1 < d; l1++)
            for (int l2 = l1 + 1; l2 < d; l2++)
                if (pi_[l1][i] == pi_[l2][i] && S[l1][i] == S[l2][i]) c++;
    return c;
}

static long total_cost(void) {
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += bfs_unreached(b * gN);
    return c + PEN * (long)dupcount();
}

static int anneal(double attempt_end, long patience) {
    random_state();
    long cost = total_cost();
    double c0 = cost > 1 ? (double)cost : 1.0;
    double start = now();
    double len = attempt_end - start;
    if (len < 0.05) len = 0.05;
    long best_c = cost, last = 0, it = 0;
    while (cost > 0) {
        if (it - last > patience) break;
        double tn = now();
        if (tn >= attempt_end) break;
        double frac = (tn - start) / len;
        double T = 0.02 * c0 * (1.0 - frac) + 0.3;
        it++;
        if (K >= 2 && rnd01() < 0.3) {
            int l = rndint(d), i1 = rndint(K), i2 = rndint(K - 1);
            if (i2 >= i1) i2++;
            int j1 = pi_[l][i1], j2 = pi_[l][i2];
            pi_[l][i1] = j2;
            pi_[l][i2] = j1;
            ipi[l][j2] = i1;
            ipi[l][j1] = i2;
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                pi_[l][i1] = j1;
                pi_[l][i2] = j2;
                ipi[l][j1] = i1;
                ipi[l][j2] = i2;
            }
        } else {
            int l = rndint(d), i = rndint(K);
            int old = S[l][i];
            int nw = rndint(gN);
            if (nw == old) continue;
            S[l][i] = nw;
            long c2 = total_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                S[l][i] = old;
            }
        }
        if (cost < best_c) {
            best_c = cost;
            last = it;
        }
    }
    return cost == 0;
}

/* Saved best configuration (group parameters, base size, pi and voltages). */
static int have = 0;
static int sK, sm, st, sr;
static int spi[MAXD][MAXK], sS[MAXD][MAXK];

static void save_state(int m, int t, int r) {
    sK = K;
    sm = m;
    st = t;
    sr = r;
    memcpy(spi, pi_, sizeof(pi_));
    memcpy(sS, S, sizeof(S));
    have = 1;
}

static void print_best(void) {
    if (!have) {
        printf("0 0\n");
        return;
    }
    K = sK;
    set_group(sm, st, sr);
    memcpy(pi_, spi, sizeof(pi_));
    memcpy(S, sS, sizeof(S));
    for (int l = 0; l < d; l++)
        for (int i = 0; i < K; i++) ipi[l][pi_[l][i]] = i;
    int kN = K * gN;
    printf("%d %d\n", 2 * kN, kN * d);
    for (int v = 0; v < kN; v++) {
        int nb[MAXD];
        nbr(v, nb);
        for (int t = 0; t < d; t++) printf("%d %d\n", v, nb[t]);
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: %s d D seed time_limit\n", argv[0]);
        return 2;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    double t0 = now();
    t_end = t0 + limit * 0.88;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 3 || d > MAXD || D < 2) {
        printf("0 0\n");
        return 0;
    }

    long moore = moore_bound();
    static const int Ks[] = {1, 2, 3, 4, 5, 6, 8, 9, 10, 12};
    const int NK = 10;
    long best_order = 0;

    while (now() < t_end && best_order < moore) {
        int k = Ks[rndint(NK)];
        long Nt = best_order / (2L * k) + 1;
        if (rnd01() < 0.4) Nt += rndint(3);
        if (Nt < 1) Nt = 1;
        if (Nt > MAXG) continue;
        if (2L * k * Nt > moore) continue;
        K = k;
        int m, t, r;
        pick_group((int)Nt, &m, &t, &r);
        set_group(m, t, r);
        double rem = t_end - now();
        if (rem <= 0) break;
        double alen = rem * 0.1;
        if (alen < 0.3) alen = 0.3;
        if (alen > rem) alen = rem;
        if (anneal(now() + alen, 3000)) {
            save_state(m, t, r);
            best_order = 2L * K * gN;
        }
    }
    print_best();
    return 0;
}
'''


# ----------------------------------------------------------------------------
# Driver.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    usable = max(1.0, 0.85 * time_limit - 2.0)
    end = t0 + usable

    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # Safe fallback: K_{d,d} has diameter 2.
    best = lib.haar_graph(d, range(d))

    def consider(n, e):
        """Adopt (n, e) if it is a larger valid graph."""
        nonlocal best
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    # Exact constructions.
    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])
            if D == 3 and lib.is_prime_power(d - 1):
                return best
    if D == 3 and d - 2 >= 3 and lib.is_prime_power(d - 2):
        try:
            ar = lib.araujo_lopez_graph(d - 2)
            consider(ar[0], ar[1])
        except (ValueError, RuntimeError):
            pass
    if D == 4 and time.monotonic() < end:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])
            if d - 1 <= 9 and lib.is_prime_power(d - 1):
                return best

    if d == 2 and D >= 2:
        n = 2 * D
        consider(n, [(i, (i + 1) % n) for i in range(n)])
        return best

    if d >= 3 and D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 2.0:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(c_budget, 2)],
                                 stdin_graph=None, timeout=c_budget + 10)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
