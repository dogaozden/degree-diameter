import itertools
import time

import lib


C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <time.h>

#define MAXN 40000
#define MAXDEG 16
#define MAXDARTS 64
#define MAXG 20000
#define MAXK2 12
#define MAXK 4
#define ITERS 60000

static int DEG, DIAM;
static int G, K2, M, R;
static int PW[MAXK2];
static int DJ[MAXDARTS], DS[MAXDARTS];
static int PM[MAXDARTS * MAXG];
static int ADJ[MAXN * MAXDEG];
static int DEGC[MAXN];
static int VIS[MAXN];
static int QU[MAXN];
static int stamp_ctr = 0;
static unsigned long long rng_state = 88172645463325252ULL;
static clock_t tstart;
static double BUDGET = 0.0;

static unsigned long long rnext(void) {
    rng_state ^= rng_state << 13;
    rng_state ^= rng_state >> 7;
    rng_state ^= rng_state << 17;
    return rng_state;
}
static int rint_(int n) { return (int)(rnext() % (unsigned long long)n); }
static double rdbl(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - tstart) / CLOCKS_PER_SEC; }

static int igcd(int a, int b) {
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

/* Semidirect product Z_M x| Z_K2, element a*K2+b, (a,b)(c,e) = (a + R^b c, b+e). */
static int gmul(int x, int y) {
    int a = x / K2, b = x % K2, c = y / K2, e = y % K2;
    return (int)(((long long)a + (long long)PW[b] * c) % M) * K2 + (b + e) % K2;
}

static void set_group(int g, int k2, int m, int r) {
    G = g; K2 = k2; M = m; R = r;
    PW[0] = 1 % M;
    for (int b = 1; b < K2; b++) PW[b] = (int)((long long)PW[b - 1] * R % M);
}

static void set_perm(int q) {
    for (int g = 0; g < G; g++) PM[q * G + g] = gmul(g, DS[q]);
}

/* Cost = (unreached (representative, vertex) pairs within DIAM) + duplicate penalty.
   Zero means the lift is simple, d-regular, bipartite and has diameter <= DIAM. */
static long long cost_eval(int k) {
    int d = DEG, n = 2 * k * G, nd = d * k;
    long long total = 0;
    for (int q1 = 0; q1 < nd; q1++)
        for (int q2 = q1 + 1; q2 < nd; q2++)
            if (q1 % k == q2 % k && DJ[q1] == DJ[q2] && DS[q1] == DS[q2])
                total += 100000;
    for (int v = 0; v < n; v++) DEGC[v] = 0;
    for (int q = 0; q < nd; q++) {
        int ia = (q % k) * G, jb = (k + DJ[q]) * G;
        const int *pm = PM + q * G;
        for (int g = 0; g < G; g++) {
            int a = ia + g, b = jb + pm[g];
            if (DEGC[a] < d) ADJ[a * d + DEGC[a]++] = b;
            if (DEGC[b] < d) ADJ[b * d + DEGC[b]++] = a;
        }
    }
    for (int r = 0; r < 2 * k; r++) {
        int src = r * G;
        if (++stamp_ctr >= 0x7ffffff0) {
            memset(VIS, 0, sizeof(VIS));
            stamp_ctr = 1;
        }
        int head = 0, tail = 0;
        QU[tail++] = src;
        VIS[src] = stamp_ctr;
        for (int lev = 0; lev < DIAM && head < tail; lev++) {
            int end = tail;
            for (int h = head; h < end; h++) {
                int u = QU[h];
                const int *au = ADJ + u * d;
                int cnt = DEGC[u];
                for (int t = 0; t < cnt; t++) {
                    int v = au[t];
                    if (VIS[v] != stamp_ctr) {
                        VIS[v] = stamp_ctr;
                        QU[tail++] = v;
                    }
                }
            }
            head = end;
        }
        total += n - tail;
    }
    return total;
}

/* Random semidirect product of order g (cyclic when K2 = 1). */
static void pick_group(int g, int *k2o, int *mo, int *ro) {
    for (int attempt = 0; attempt < 30; attempt++) {
        int k2 = 1 + rint_(MAXK2);
        if (g % k2) continue;
        int m = g / k2;
        if (m < 2) continue;
        if (k2 == 1) { *k2o = 1; *mo = m; *ro = 1; return; }
        int cnt = 0;
        for (int r = 1; r < m; r++)
            if (igcd(r, m) == 1 && powmod(r, k2, m) == 1 % m) cnt++;
        if (!cnt) continue;
        int pick = rint_(cnt);
        for (int r = 1; r < m; r++) {
            if (igcd(r, m) == 1 && powmod(r, k2, m) == 1 % m) {
                if (pick == 0) { *k2o = k2; *mo = m; *ro = r; return; }
                pick--;
            }
        }
    }
    *k2o = 1; *mo = g; *ro = 1;
}

/* Each layer is a permutation of the k base B-vertices, so every vertex has degree DEG. */
static void init_state(int k) {
    int d = DEG;
    for (int l = 0; l < d; l++) {
        int p[MAXK];
        for (int i = 0; i < k; i++) p[i] = i;
        for (int i = k - 1; i > 0; i--) {
            int j = rint_(i + 1), t = p[i];
            p[i] = p[j];
            p[j] = t;
        }
        for (int i = 0; i < k; i++) DJ[l * k + i] = p[i];
    }
    for (int q = 0; q < d * k; q++) {
        DS[q] = rint_(G);
        set_perm(q);
    }
}

/* Simulated annealing over one group/base shape. Returns the final cost. */
static long long anneal(int k, int g) {
    int d = DEG, nd = d * k;
    init_state(k);
    long long cost = cost_eval(k);
    for (int t = 0; t < ITERS && cost > 0; t++) {
        if ((t & 255) == 0 && elapsed() >= BUDGET) break;
        double T = 2.0 * pow(0.02, (double)t / ITERS) + 0.02;
        int type = (k >= 2 && rdbl() < 0.35) ? 1 : 0;
        int q1 = 0, q2 = 0, olds = 0;
        if (type == 1) {
            int l = rint_(d);
            int i1 = rint_(k), i2 = rint_(k);
            if (i1 == i2) continue;
            q1 = l * k + i1;
            q2 = l * k + i2;
            int tmp = DJ[q1]; DJ[q1] = DJ[q2]; DJ[q2] = tmp;
        } else {
            q1 = rint_(nd);
            olds = DS[q1];
            DS[q1] = rint_(g);
            set_perm(q1);
        }
        long long c2 = cost_eval(k);
        if (c2 <= cost || rdbl() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            if (type == 1) {
                int tmp = DJ[q1]; DJ[q1] = DJ[q2]; DJ[q2] = tmp;
            } else {
                DS[q1] = olds;
                set_perm(q1);
            }
        }
    }
    return cost;
}

static void print_lift(int k, int g, int k2, int m, int r,
                       const int *dj, const int *ds) {
    set_group(g, k2, m, r);
    int nd = DEG * k;
    for (int q = 0; q < nd; q++) {
        DJ[q] = dj[q];
        DS[q] = ds[q];
        set_perm(q);
    }
    printf("%d %d\n", 2 * k * G, nd * G);
    for (int q = 0; q < nd; q++) {
        int i = q % k, j = DJ[q];
        for (int x = 0; x < G; x++)
            printf("%d %d\n", i * G + x, (k + j) * G + gmul(x, DS[q]));
    }
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    int d = atoi(argv[1]), D = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    BUDGET = atof(argv[4]);
    tstart = clock();
    rng_state ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rng_state == 0) rng_state = 1;
    for (int w = 0; w < 10; w++) rnext();

    /* Optional start graph: its order is the bar that a lift must beat. */
    int sn = 0, sm = 0;
    int *se = NULL;
    if (scanf("%d %d", &sn, &sm) != 2) { sn = 0; sm = 0; }
    if (sn < 0 || sm < 0) { sn = 0; sm = 0; }
    if (sm > 0) {
        se = (int *)malloc(sizeof(int) * 2 * (size_t)sm);
        int ok = 1;
        for (int e = 0; e < 2 * sm; e++)
            if (scanf("%d", &se[e]) != 1) { ok = 0; break; }
        if (!ok) { sn = 0; sm = 0; }
    }

    DEG = d;
    DIAM = D;
    int best_n = sn;
    int have = 0;
    int bK = 0, bG = 0, bK2 = 0, bM = 0, bR = 0;
    static int bDJ[MAXDARTS], bDS[MAXDARTS];

    if (d >= 1 && d <= MAXDEG && D >= 2) {
        static const int kc[5] = {1, 1, 2, 2, 3};
        while (elapsed() < BUDGET) {
            int k = kc[rint_(5)];
            int base = best_n / (2 * k);
            int spread = base / 6 + 1;
            if (spread < 3) spread = 3;
            int g = base + 1 + rint_(spread);   /* lift order just above the bar */
            if (g < 2) g = 2;
            if (g > MAXG || 2 * k * g > MAXN) continue;
            int k2, m, r;
            pick_group(g, &k2, &m, &r);
            set_group(g, k2, m, r);
            long long cost = anneal(k, g);
            if (cost == 0 && 2 * k * g > best_n) {
                best_n = 2 * k * g;
                have = 1;
                bK = k; bG = g; bK2 = k2; bM = m; bR = r;
                for (int q = 0; q < d * k; q++) {
                    bDJ[q] = DJ[q];
                    bDS[q] = DS[q];
                }
            }
        }
    }

    if (have) {
        print_lift(bK, bG, bK2, bM, bR, bDJ, bDS);
    } else if (sn > 0) {
        printf("%d %d\n", sn, sm);
        for (int e = 0; e < sm; e++) printf("%d %d\n", se[2 * e], se[2 * e + 1]);
    } else {
        printf("2 1\n0 1\n");
    }
    free(se);
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

    if D >= 3:
        pg = _best_pg(d)
        if pg is not None:
            consider(pg[0], pg[1])

    if D >= 4 and time.monotonic() - t0 < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing larger is possible.
    if best_n >= lib.moore_bound(d, D):
        return best

    # Main search in C: annealed voltage lifts of semidirect products,
    # with an escalating target order above the best graph found so far.
    budget = 0.82 * time_limit - (time.monotonic() - t0) - 2.0
    if budget >= 2.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed & 0xFFFFFFFF, round(budget, 2)],
                            stdin_graph=best, timeout=budget + 8.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
