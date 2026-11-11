"""Multi-base voltage lifts over semidirect groups for the bipartite degree-diameter problem.

Replaces the affine Haar search. The new family is a bipartite lift of a small base
graph with t vertices per side (t = 1..4). The base is d-regular, built as d layers,
each a permutation sigma_r of {0..t-1} with a voltage v_{r,i} in a group G of order n:
(A,i,g) ~ (B,sigma_r(i), g*v_{r,i}). G = Z_m x|_r Z_k is chosen at random, and the
lift has 2*t*n vertices. Left multiplication by G is an automorphism, so the diameter
check needs only 2t BFS runs, from (A,i,e) and (B,j,e).

The C engine climbs total vertex counts T = 2tn upward from a lower bound. For each T
it tries random (t, G) pairs and runs simulated annealing over the voltages to drive
the number of pairs at distance > D to zero. The largest valid graph found is printed.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-base voltage lift search over semidirect groups Z_m x|_r Z_k.
 * Usage: prog d D seed time_limit Tlo Thi     (stdin ignored)
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXV 20000
#define MAXD 32
#define MAXT 4
#define GMAX 2
#define ITERS 2000
#define SLICE 0.8

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

/* ------------------------------------------------------------ group Z_m x|_r Z_k */

/* Element (a,b) is coded a*k+b. Product: (a1,b1)(a2,b2) = (a1 + r^b1 a2, b1 + b2). */
static int gm, gk, gr;
static int PW[MAXV];

static void setup_group(int m, int k, int r) {
    gm = m;
    gk = k;
    gr = r;
    PW[0] = 1 % m;
    for (int b = 1; b < k; b++) PW[b] = (int)((long long)PW[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a1 = x / gk, b1 = x % gk, a2 = y / gk, b2 = y % gk;
    int a = (int)(((long long)a1 + (long long)PW[b1] * a2) % gm);
    int b = (b1 + b2) % gk;
    return a * gk + b;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* Random group of order n: random divisor k, random r (falls back to r = 1). */
static void sample_group(int n, int *om, int *ok, int *orr) {
    static int divs[512];
    int nd = 0;
    for (int i = 1; (long long)i * i <= n; i++)
        if (n % i == 0) {
            divs[nd++] = i;
            if (i * i != n) divs[nd++] = n / i;
        }
    int k = divs[rndint(nd)];
    int m = n / k;
    int r = (m > 1) ? 1 : 0;
    if (m > 1) {
        for (int tr = 0; tr < 200; tr++) {
            int c = 1 + rndint(m - 1);
            if (gcdi(c, m) == 1 && powmod(c, k, m) == 1 % m) { r = c; break; }
        }
    }
    *om = m;
    *ok = k;
    *orr = r;
}

/* ------------------------------------------------------------ lift state */

static int T_base, nB;                 /* base vertices per side, group order */
static int sig[MAXD][MAXT];            /* layer permutations */
static int volt[MAXD][MAXT];           /* voltages */
static int nbA[MAXV * MAXD];           /* A-vertex (i*n+g) -> B neighbours, slot r */
static int nbB[MAXV * MAXD];           /* B-vertex (j*n+h) -> A neighbours, slot r */
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

/* Dart r from A-base i to B-base sigma_r(i) with voltage v:
 * (A,i,g) ~ (B,j,g*v). Fill both sides for this (r,i). */
static void fill_slot(int r, int i) {
    int n = nB, t = T_base;
    int j = sig[r][i], v = volt[r][i];
    for (int g = 0; g < n; g++) {
        int h = gmul(g, v);
        nbA[(i * n + g) * d + r] = t * n + j * n + h;
        nbB[(j * n + h) * d + r] = i * n + g;
    }
}

static void fill_all(void) {
    for (int r = 0; r < d; r++)
        for (int i = 0; i < T_base; i++) fill_slot(r, i);
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int tn = T_base * nB;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            const int *nb = (v < tn) ? &nbA[v * d] : &nbB[(v - tn) * d];
            for (int r = 0; r < d; r++) {
                int u = nb[r];
                if (vis[u] != stamp_) {
                    vis[u] = stamp_;
                    que[tail++] = u;
                }
            }
        }
    }
    return tail;
}

/* Left-multiplication symmetry: two BFS runs per base vertex decide the diameter.
 * Cost is the number of unreached (source, vertex) pairs. */
static long cover_cost(void) {
    int tn = T_base * nB;
    int V = 2 * tn;
    long c = 0;
    for (int i = 0; i < T_base; i++) c += V - bfs_count(i * nB);
    for (int j = 0; j < T_base; j++) c += V - bfs_count(tn + j * nB);
    return c;
}

static void random_perms(void) {
    for (int r = 0; r < d; r++) {
        int p[MAXT];
        for (int i = 0; i < T_base; i++) p[i] = i;
        for (int i = T_base - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = p[i];
            p[i] = p[j];
            p[j] = tmp;
        }
        for (int i = 0; i < T_base; i++) sig[r][i] = p[i];
    }
}

/* Simulated annealing over permutations (restarts) and voltages.
 * Returns 1 when cost 0 is reached; the current state is then the solution. */
static int search_group(double until) {
    while (now() < until) {
        random_perms();
        for (int r = 0; r < d; r++)
            for (int i = 0; i < T_base; i++) volt[r][i] = rndint(nB);
        fill_all();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double temp = Ts * pow(Te / Ts, (double)it / ITERS);
            int rr = rndint(d), ii = rndint(T_base);
            int x = rndint(nB);
            int old = volt[rr][ii];
            if (x == old) continue;
            volt[rr][ii] = x;
            fill_slot(rr, ii);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / temp)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                volt[rr][ii] = old;
                fill_slot(rr, ii);
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ best solution */

static int bestFound = 0, bt, bn, bm, bk, br;
static int bsig[MAXD][MAXT], bvolt[MAXD][MAXT];

static void save_best(int t, int n, int m, int k, int r) {
    bestFound = 1;
    bt = t;
    bn = n;
    bm = m;
    bk = k;
    br = r;
    memcpy(bsig, sig, sizeof sig);
    memcpy(bvolt, volt, sizeof volt);
}

/* Returns 1 if dart r at A-vertex (i,g) duplicates an earlier dart (same neighbour). */
static int is_dup(int i, int g, int r) {
    int j = bsig[r][i], h = gmul(g, bvolt[r][i]);
    for (int r2 = 0; r2 < r; r2++)
        if (bsig[r2][i] == j && gmul(g, bvolt[r2][i]) == h) return 1;
    return 0;
}

static void print_best(void) {
    setup_group(bm, bk, br);
    int t = bt, n = bn, tn = t * n;
    long cnt = 0;
    for (int i = 0; i < t; i++)
        for (int g = 0; g < n; g++)
            for (int r = 0; r < d; r++)
                if (!is_dup(i, g, r)) cnt++;
    printf("%d %ld\n", 2 * tn, cnt);
    for (int i = 0; i < t; i++)
        for (int g = 0; g < n; g++)
            for (int r = 0; r < d; r++)
                if (!is_dup(i, g, r))
                    printf("%d %d\n", i * n + g,
                           tn + bsig[r][i] * n + gmul(g, bvolt[r][i]));
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 7) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long long lo = atoll(argv[5]), hi = atoll(argv[6]);
    t_end = now() + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXV) hi = MAXV;
    if (lo < 2 * d) lo = 2 * d;
    if (lo & 1) lo++;

    /* Climb total vertex counts T = 2*t*n upward; keep the largest success. */
    for (long long T = lo; T <= hi; T += 2) {
        if (now() > t_end) break;
        int done = 0;
        for (int t = 1; t <= MAXT && !done; t++) {
            if (((T / 2) % t) != 0) continue;
            int n = (int)(T / (2 * t));
            if (n < 2) continue;
            for (int gi = 0; gi < GMAX && !done; gi++) {
                double rem = t_end - now();
                if (rem <= 0) break;
                int m, k, r;
                sample_group(n, &m, &k, &r);
                setup_group(m, k, r);
                T_base = t;
                nB = n;
                double slice = SLICE < rem ? SLICE : rem;
                if (search_group(now() + slice)) {
                    save_best(t, n, m, k, r);
                    done = 1;
                }
            }
        }
    }

    if (!bestFound) {
        printf("0 0\n");
        return 0;
    }
    print_best();
    return 0;
}
'''


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
    """W(q) for the largest prime power q with q + 1 <= d (kept small for speed)."""
    for q in range(min(d - 1, 7), 1, -1):
        if lib.is_prime_power(q):
            return _gq_w(q)
    return None


def build(d, D, seed, time_limit):
    t0 = time.monotonic()
    if d < 1 or D < 1:
        return 1, []
    if D == 1:
        return 2, [(0, 1)]

    # K_{d,d} has diameter 2, so it is valid for every D >= 2 and is the safe fallback.
    best = lib.haar_graph(d, range(d))

    def consider(cand):
        nonlocal best
        if cand is None:
            return
        n, e = cand
        if n > best[0] and lib.is_valid(n, e, d, D):
            best = (n, e)

    if D >= 3:
        try:
            consider(_best_pg(d))
        except Exception:
            pass
        # Exact Moore graph: nothing can beat it.
        if D == 3 and lib.is_prime_power(d - 1) and best[0] > 2 * d:
            return best
        if d - 2 >= 3 and lib.is_prime_power(d - 2):
            try:
                consider(lib.araujo_lopez_graph(d - 2))
            except Exception:
                pass

    if D == 4:
        try:
            consider(_best_gq(d))
        except Exception:
            pass

    # New search: multi-base voltage lifts over semidirect groups.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 1, mb // 4)
        hi = min(mb, 20000)
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
