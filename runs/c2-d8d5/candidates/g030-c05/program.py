"""Bold variant: large-base bi-Cayley lift annealing in C, with exact constructions and a valid fallback."""
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
# C engine: bi-Cayley lifts over Z_m x| Z_k with p base vertices per side.
# Layer t is a permutation dj[t] of the base (a d-regular base multigraph),
# each dart carries a group voltage. Validity is checked from the 2p
# representative vertices only: the group acts transitively on each side,
# so the graph has diameter <= D iff every representative reaches everything.
# Simulated annealing on (unreached pairs + duplicate-dart penalty).
# ----------------------------------------------------------------------------

C_LIFT = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 4096
#define MAXD 16
#define MAXP 8
#define ITERS 80000L

static int d, D;
static long MOORE;
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

static long powmod(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    if (b < 0) b += m;
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

/* Z_m x|_r Z_k, element (a,b) coded as a*k+b, (a,b)(c,e) = (a + r^b c, b+e). */
typedef struct {
    int m, k, r;
    int rp[MAXV];
} Grp;

static void set_group(Grp *G, int m, int k, int r) {
    G->m = m;
    G->k = k;
    G->r = r;
    G->rp[0] = 1 % m;
    for (int b = 1; b < k; b++) G->rp[b] = (int)((long)G->rp[b - 1] * r % m);
}

static int gmul(const Grp *G, int x, int y) {
    int a = x / G->k, b = x % G->k, c = y / G->k, e = y % G->k;
    long t = ((long)a + (long)G->rp[b] * c) % G->m;
    return (int)(t * G->k + (b + e) % G->k);
}

static int ginv(const Grp *G, int x) {
    int a = x / G->k, b = x % G->k;
    int nb = (G->k - b) % G->k;
    long t = (-(long)G->rp[nb] * a) % G->m;
    if (t < 0) t += G->m;
    return (int)(t * G->k + nb);
}

static void choose_group(int N, Grp *G) {
    for (int attempt = 0; attempt < 60; attempt++) {
        int k = 1;
        if (rndint(3) > 0) {
            int ds[MAXV], nd = 0;
            for (int x = 1; x <= N; x++)
                if (N % x == 0) ds[nd++] = x;
            k = ds[rndint(nd)];
        }
        if (k == 1) break;
        int m = N / k;
        int r = (m <= 2) ? 1 % m : 1 + rndint(m - 1);
        if (gcd(r, m) == 1 && powmod(r, k, m) == 1 % m) {
            set_group(G, m, k, r);
            return;
        }
    }
    set_group(G, N, 1, 1);
}

/* Lift state: layer t sends A-vertex i to B-vertex DJ[t][i] with voltage DG[t][i]. */
static int DJ[MAXD][MAXP], DG[MAXD][MAXP], II[MAXD][MAXP];
static int nb[MAXV][MAXD];
static int dist_[MAXV], qu[MAXV];

static long unreached(int n, int s) {
    for (int v = 0; v < n; v++) dist_[v] = -1;
    int h = 0, tl = 0, cnt = 1;
    dist_[s] = 0;
    qu[tl++] = s;
    while (h < tl) {
        int v = qu[h++];
        if (dist_[v] >= D) continue;
        for (int t = 0; t < d; t++) {
            int u = nb[v][t];
            if (dist_[u] < 0) {
                dist_[u] = dist_[v] + 1;
                qu[tl++] = u;
                cnt++;
            }
        }
    }
    return n - cnt;
}

static long eval_lift(int p, int N, const Grp *G) {
    int n = 2 * p * N;
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < p; i++)
            for (int x = 0; x < N; x++)
                nb[i * N + x][t] = p * N + DJ[t][i] * N + gmul(G, x, DG[t][i]);
        for (int j = 0; j < p; j++) {
            int i = II[t][j];
            int gi = ginv(G, DG[t][i]);
            for (int y = 0; y < N; y++)
                nb[p * N + j * N + y][t] = i * N + gmul(G, y, gi);
        }
    }
    long dup = 0;
    for (int i = 0; i < p; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (DJ[t][i] == DJ[t2][i] && DG[t][i] == DG[t2][i]) dup++;
    long cost = 0;
    for (int i = 0; i < p; i++) cost += unreached(n, i * N);
    for (int j = 0; j < p; j++) cost += unreached(n, p * N + j * N);
    return cost + (long)n * dup;
}

static int lift_sa(int p, int N, const Grp *G, double until) {
    for (int t = 0; t < d; t++) {
        int perm[MAXP];
        for (int i = 0; i < p; i++) perm[i] = i;
        for (int i = p - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int s = perm[i]; perm[i] = perm[j]; perm[j] = s;
        }
        for (int i = 0; i < p; i++) {
            DJ[t][i] = perm[i];
            II[t][perm[i]] = i;
            DG[t][i] = rndint(N);
        }
    }
    long cost = eval_lift(p, N, G);
    long it = 0;
    while (cost > 0) {
        if ((it & 63) == 0 && now() > until) return 0;
        double frac = (double)it / (double)ITERS;
        if (frac > 1.0) frac = 1.0;
        double T = 0.4 + 3.0 * (1.0 - frac);
        it++;
        if (p < 2 || rndint(10) < 7) {
            int t = rndint(d), i = rndint(p);
            int old = DG[t][i];
            int nw = rndint(N - 1);
            if (nw >= old) nw++;
            DG[t][i] = nw;
            long nc = eval_lift(p, N, G);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else DG[t][i] = old;
        } else {
            int t = rndint(d), i1 = rndint(p), i2 = rndint(p - 1);
            if (i2 >= i1) i2++;
            int a = DJ[t][i1], b = DJ[t][i2];
            DJ[t][i1] = b; DJ[t][i2] = a;
            II[t][b] = i1; II[t][a] = i2;
            long nc = eval_lift(p, N, G);
            if (nc <= cost || rnd01() < exp(-(double)(nc - cost) / T)) cost = nc;
            else {
                DJ[t][i1] = a; DJ[t][i2] = b;
                II[t][a] = i1; II[t][b] = i2;
            }
        }
    }
    return 1;
}

static int SDJ[MAXD][MAXP], SDG[MAXD][MAXP];
static Grp SG;
static int SP, SN;

int main(int argc, char **argv) {
    if (argc < 5) return 2;
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long floor_n = argc > 5 ? atol(argv[5]) : 0;
    double t_end = now() + limit;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || D < 2 || d > MAXD) { printf("0 0\n"); return 0; }
    MOORE = moore_bound();
    if (MOORE > MAXV) MOORE = MAXV;

    long best_n = floor_n;
    int have = 0;
    while (now() < t_end) {
        long target = best_n + 2;
        if (target > MOORE) break;
        int p = 1 + rndint(MAXP);
        long N = (target + 2L * p - 1) / (2L * p) + rndint(2);
        if (N < 2) N = 2;
        while (N > 1 && 2L * p * N > MOORE) N--;
        if (2L * p * N <= best_n || 2L * p * N > MOORE) continue;
        Grp G;
        choose_group((int)N, &G);
        double until = now() + 6.0 + 6.0 * rnd01();
        if (until > t_end) until = t_end;
        if (lift_sa(p, (int)N, &G, until)) {
            best_n = 2L * p * N;
            memcpy(SDJ, DJ, sizeof(DJ));
            memcpy(SDG, DG, sizeof(DG));
            SG = G;
            SP = p;
            SN = (int)N;
            have = 1;
        }
    }

    if (!have) { printf("0 0\n"); return 0; }
    memcpy(DJ, SDJ, sizeof(DJ));
    memcpy(DG, SDG, sizeof(DG));
    for (int t = 0; t < d; t++)
        for (int i = 0; i < SP; i++) II[t][DJ[t][i]] = i;
    eval_lift(SP, SN, &SG);
    int n = 2 * SP * SN;
    int A = SP * SN;
    long m = (long)A * d;
    printf("%d %ld\n", n, m);
    for (int u = 0; u < A; u++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", u, nb[u][t]);
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

    # Bold search: C lift annealing over larger base multigraphs, seeded with the
    # current best order as a floor.
    if d >= 2 and D >= 2:
        c_budget = end - time.monotonic() - 0.5
        if c_budget > 1.0:
            try:
                text = lib.run_c(C_LIFT, [d, D, seed, round(c_budget, 2), best[0]],
                                 stdin_graph=None, timeout=c_budget + 8)
                out = lib.parse_graph_text(text)
                consider(out[0], out[1])
            except (RuntimeError, ValueError):
                pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
