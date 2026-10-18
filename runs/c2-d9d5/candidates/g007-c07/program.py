"""Multi-base voltage lifts over semidirect groups for the bipartite degree-diameter problem.

Construction: take NA left base vertices and NA right base vertices. Each left base vertex
has d darts. Dart t from left i to right j(t) carries a voltage g(t) in a group
G = Z_m x| Z_k of order N. The lift has 2*NA*N vertices: left (i,x) is adjacent to
right (j(t), x*g(t)) for each dart t of i. Each right vertex gets exactly d neighbours.
Darts in the same (i,j) block have distinct voltages, so the lift is simple.

Left and right translations are automorphisms, so the diameter is at most D iff BFS
from each of the 2*NA base identities reaches everything within D steps. Simulated
annealing changes voltages and group choices to reduce the number of unreached pairs.

Previous families used a single base pair (Haar graphs). This version uses 1 to 4 base
vertices per side, so the group order is only a fraction of the total order. The search
covers a range of total orders and keeps the largest valid lift found.
"""
import itertools
import time

import lib

C_SOURCE = r'''
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXD 16
#define MAXA 4
#define MAXT 12000
#define MAXK 6000
#define MAXDARTS (MAXA * MAXD)

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

/* ------------------------------------------------------------ group Z_GM x| Z_GK
 * Element (a,b) is coded a*GK+b. Product: (a,b)(c,e) = (a + r^b c, b+e), r^GK = 1 mod GM. */

static int GM, GK, GR, GORD;
static int powr[MAXK];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GR = r;
    GORD = m * k;
    long p = 1 % m;
    for (int b = 0; b < k; b++) {
        powr[b] = (int)p;
        p = (p * r) % m;
    }
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (a + (int)(((long)powr[b] * c) % GM)) % GM;
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int na = (int)(((long)powr[nb] * a) % GM);
    na = (GM - na) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ lift structure */

static int NA;                                  /* left base vertices = right base vertices */
static int jt[MAXDARTS], gt[MAXDARTS], rslot[MAXDARTS];
static int rleft[MAXDARTS], rinv[MAXDARTS];     /* indexed by right dart rd = j*d + slot */

/* Left vertex i has darts t = i*d + s. Each round s assigns a random permutation of the
 * left bases to right bases, so every right vertex receives exactly d darts. */
static void build_structure(int na) {
    NA = na;
    int nd = na * d;
    int perm[MAXA];
    for (int r = 0; r < d; r++) {
        for (int i = 0; i < na; i++) perm[i] = i;
        for (int i = na - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < na; i++) jt[i * d + r] = perm[i];
    }
    int rc[MAXA];
    for (int j = 0; j < na; j++) rc[j] = 0;
    for (int t = 0; t < nd; t++) {
        int j = jt[t];
        rslot[t] = rc[j]++;
        rleft[j * d + rslot[t]] = t / d;
    }
}

/* Darts in one (i,j) block need distinct voltages (otherwise the lift has parallel edges). */
static int dart_ok(int t, int g) {
    int i = t / d;
    for (int s = 0; s < d; s++) {
        int t2 = i * d + s;
        if (t2 != t && jt[t2] == jt[t] && gt[t2] == g) return 0;
    }
    return 1;
}

static void set_dart(int t, int g) {
    gt[t] = g;
    int rd = jt[t] * d + rslot[t];
    rinv[rd] = ginv(g);
}

static void random_darts(void) {
    int nd = NA * d;
    for (int t = 0; t < nd; t++) gt[t] = -1;
    for (int t = 0; t < nd; t++) {
        int g;
        do { g = rndint(GORD); } while (!dart_ok(t, g));
        set_dart(t, g);
    }
}

/* ------------------------------------------------------------ BFS and cost */

static int seen[MAXT], stampv = 0, que[MAXT];

/* Number of vertices within distance D of src. Left ids: i*GORD+x. Right ids: NA*GORD+j*GORD+y. */
static int reach_count(int src) {
    int AG = NA * GORD;
    stampv++;
    int head = 0, tail = 0;
    que[tail++] = src;
    seen[src] = stampv;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < AG) {
                int i = v / GORD, x = v % GORD;
                for (int s = 0; s < d; s++) {
                    int t = i * d + s;
                    int u = AG + jt[t] * GORD + gmul(x, gt[t]);
                    if (seen[u] != stampv) {
                        seen[u] = stampv;
                        que[tail++] = u;
                    }
                }
            } else {
                int w = v - AG, j = w / GORD, y = w % GORD;
                for (int s = 0; s < d; s++) {
                    int rd = j * d + s;
                    int u = rleft[rd] * GORD + gmul(y, rinv[rd]);
                    if (seen[u] != stampv) {
                        seen[u] = stampv;
                        que[tail++] = u;
                    }
                }
            }
        }
    }
    return tail;
}

/* Automorphisms (left and right translations) make BFS from each base identity enough. */
static long cost_all(void) {
    int V = 2 * NA * GORD, AG = NA * GORD;
    long c = 0;
    for (int i = 0; i < NA; i++) c += V - reach_count(i * GORD);
    for (int j = 0; j < NA; j++) c += V - reach_count(AG + j * GORD);
    return c;
}

/* Simulated annealing over the voltages of the current structure and group.
 * Returns 1 when diameter <= D holds (cost 0), 0 on timeout. */
static int search(double until) {
    int nd = NA * d;
    while (now() < until) {
        random_darts();
        long cost = cost_all();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 4000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(nd);
            int old = gt[t];
            int g;
            do { g = rndint(GORD); } while (g == old || !dart_ok(t, g));
            set_dart(t, g);
            long c2 = cost_all();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ choosing a group */

static long gcdl(long a, long b) {
    while (b) {
        long t = a % b;
        a = b;
        b = t;
    }
    return a;
}

static long powmodl(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int rl[MAXT];

/* Random Z_m x| Z_k with m*k = N, m >= 2, k >= 1, and r with gcd(r,m)=1, r^k = 1 mod m. */
static int pick_group(int N, int *om, int *ok, int *orr) {
    int divs[128], nd = 0;
    for (int k = 1; k <= N && nd < 128; k++)
        if (N % k == 0 && N / k >= 2) divs[nd++] = k;
    if (nd == 0) return 0;
    for (int tries = 0; tries < 12; tries++) {
        int k = divs[rndint(nd)];
        int m = N / k;
        int cnt = 0;
        for (int r = 1; r < m; r++)
            if (gcdl(r, m) == 1 && powmodl(r, k, m) == 1 % m) rl[cnt++] = r;
        if (!cnt) continue;
        *om = m;
        *ok = k;
        *orr = rl[rndint(cnt)];
        return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best result */

static int bestT = 0, bNA, bGM, bGK, bGR;
static int bJt[MAXDARTS], bGt[MAXDARTS];

static void print_best(void) {
    setup_group(bGM, bGK, bGR);
    int G = GORD;
    int n = 2 * bNA * G, m = bNA * G * d;
    printf("%d %d\n", n, m);
    int AG = bNA * G;
    for (int i = 0; i < bNA; i++)
        for (int x = 0; x < G; x++)
            for (int s = 0; s < d; s++) {
                int t = i * d + s;
                int v = AG + bJt[t] * G + gmul(x, bGt[t]);
                printf("%d %d\n", i * G + x, v);
            }
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
    int lo = atoi(argv[5]), hi = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi > MAXT) hi = MAXT;
    if (lo < 4 * d) lo = 4 * d;
    if (lo & 1) lo++;

    int stop = 0;
    for (int pass = 0; pass < 1000000 && !stop; pass++) {
        int attempted = 0;
        for (int T = lo; T <= hi && !stop; T += 2) {
            if (T <= bestT) continue;
            for (int a = 1; a <= MAXA; a++) {
                if (T % (2 * a)) continue;
                int N = T / (2 * a);
                if (N < 2 * d || N > MAXK) continue;
                double rem = t_end - now();
                if (rem < 0.2) {
                    stop = 1;
                    break;
                }
                double slice = 0.15 * rem;
                if (slice < 0.3) slice = 0.3;
                if (slice > 2.0) slice = 2.0;
                if (slice > rem) slice = rem;
                int m, k, r;
                if (!pick_group(N, &m, &k, &r)) continue;
                setup_group(m, k, r);
                build_structure(a);
                attempted = 1;
                if (search(now() + slice)) {
                    int nd = a * d;
                    bestT = T;
                    bNA = a;
                    bGM = m;
                    bGK = k;
                    bGR = r;
                    for (int q = 0; q < nd; q++) {
                        bJt[q] = jt[q];
                        bGt[q] = gt[q];
                    }
                    break;
                }
            }
        }
        if (!attempted) break;
    }

    if (bestT == 0) {
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

    # Search: multi-base voltage lifts over semidirect groups (1 to 4 base vertices per side).
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 2, int(0.2 * mb))
        hi = min(mb, 6000)
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
