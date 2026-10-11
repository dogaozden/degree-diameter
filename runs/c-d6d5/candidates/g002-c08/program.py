import itertools
import time

import lib


# Phase 1: voltage-lift search over semidirect products (the proven engine).
C_LIFT = r"""
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
#define ITERS 200000

static int DEG, DIAM;
static int KB, G, K2, M, R;
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
    return ((a + PW[b] * c) % M) * K2 + (b + e) % K2;
}

static void set_group(int g, int k2, int m, int r) {
    G = g; K2 = k2; M = m; R = r;
    PW[0] = 1 % M;
    for (int b = 1; b < K2; b++) PW[b] = (int)((long long)PW[b - 1] * R % M);
}

static void set_perm(int q) {
    for (int g = 0; g < G; g++) PM[q * G + g] = gmul(g, DS[q]);
}

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

static int pick_group(int g, int *k2o, int *mo, int *ro) {
    for (int attempt = 0; attempt < 30; attempt++) {
        int k2 = 1 + rint_(MAXK2);
        if (g % k2) continue;
        int m = g / k2;
        if (m < 2) continue;
        if (k2 == 1) { *k2o = 1; *mo = m; *ro = 1; return 1; }
        int cnt = 0;
        for (int r = 1; r < m; r++)
            if (igcd(r, m) == 1 && powmod(r, k2, m) == 1 % m) cnt++;
        if (!cnt) continue;
        int pick = rint_(cnt);
        for (int r = 1; r < m; r++) {
            if (igcd(r, m) == 1 && powmod(r, k2, m) == 1 % m) {
                if (pick == 0) { *k2o = k2; *mo = m; *ro = r; return 1; }
                pick--;
            }
        }
    }
    *k2o = 1; *mo = g; *ro = 1;
    return 1;
}

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
    double budget = atof(argv[4]);
    tstart = clock();
    rng_state ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rng_state == 0) rng_state = 1;
    for (int w = 0; w < 10; w++) rnext();

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
        int kchoice[6] = {1, 1, 1, 2, 2, 3};
        while (elapsed() < budget) {
            int k = kchoice[rint_(6)];
            int base = best_n / (2 * k);
            int spread = base / 6 + 1;
            if (spread < 3) spread = 3;
            int g = base + 1 + rint_(spread);
            if (g < 2) g = 2;
            if (g > MAXG || 2 * k * g > MAXN) continue;
            int k2, m, r;
            pick_group(g, &k2, &m, &r);
            set_group(g, k2, m, r);
            KB = k;
            init_state(k);
            int nd = d * k;
            long long cost = cost_eval(k);
            for (int t = 0; t < ITERS && cost > 0; t++) {
                if ((t & 255) == 0 && elapsed() >= budget) break;
                double T = 3.0 * pow(0.03, (double)t / ITERS);
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
            if (cost == 0) {
                best_n = 2 * k * g;
                have = 1;
                bK = k; bG = g; bK2 = k2; bM = m; bR = r;
                for (int q = 0; q < nd; q++) {
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


# Phase 2: free (non-lifted) annealing. Starts from a valid bipartite d-regular-ish
# graph, adds vertex pairs by splicing in d edges, and repairs diameter with
# degree-preserving edge switches. Cost = ordered pairs farther than D apart,
# computed exactly with bitset BFS.
C_ANNEAL = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <math.h>
#include <stdint.h>
#include <time.h>

#define MAXN 4096
#define MAXW 64
#define MAXD 16
#define MAXE 40000
#define LSCHED 4000
#define T0 30.0
#define T1 0.5

static int DEGD, DIAM, NN, EE;
static int DEGV[MAXN];
static int ADJ[MAXN * MAXD];
static int EA[MAXE], EB[MAXE];
static int SU[MAXE], SV[MAXE];
static int BEA[MAXE], BEB[MAXE];
static int bestN = 0, bestE = 0, have = 0;
static uint64_t BA[MAXN * MAXW], BB[MAXN * MAXW];
static uint64_t *CUR = BA, *NXT = BB;
static int usedA[MAXN], usedB[MAXN];
static int stamp_ = 0;
static clock_t tstart;
static double budget;
static unsigned long long rs = 88172645463325252ULL;

static unsigned long long rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnext() % (unsigned long long)n); }
static double rdbl(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - tstart) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static int has_edge(int a, int b) {
    for (int i = 0; i < DEGV[a]; i++)
        if (ADJ[a * MAXD + i] == b) return 1;
    return 0;
}

static void rep(int v, int old, int nw) {
    for (int i = 0; i < DEGV[v]; i++)
        if (ADJ[v * MAXD + i] == old) { ADJ[v * MAXD + i] = nw; return; }
}

static void addn(int v, int w) {
    ADJ[v * MAXD + DEGV[v]] = w;
    DEGV[v]++;
}

/* Edge e1 = (a1,b1), e2 = (a2,b2) become (a1,b2), (a2,b1). Applying it twice
   to the same pair of edge slots restores the original graph. */
static void sw(int e1, int e2) {
    int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
    rep(a1, b1, b2);
    rep(b1, a1, a2);
    rep(a2, b2, b1);
    rep(b2, a2, a1);
    EB[e1] = b2;
    EB[e2] = b1;
}

static long long eval(void) {
    int N = NN, W = (N + 63) >> 6;
    for (int v = 0; v < N; v++) {
        uint64_t *r = CUR + (size_t)v * W;
        for (int w = 0; w < W; w++) r[w] = 0;
        r[v >> 6] |= 1ULL << (v & 63);
    }
    for (int rd = 0; rd < DIAM; rd++) {
        for (int v = 0; v < N; v++) {
            uint64_t *nx = NXT + (size_t)v * W;
            const uint64_t *cu = CUR + (size_t)v * W;
            for (int w = 0; w < W; w++) nx[w] = cu[w];
            for (int i = 0; i < DEGV[v]; i++) {
                const uint64_t *cn = CUR + (size_t)ADJ[v * MAXD + i] * W;
                for (int w = 0; w < W; w++) nx[w] |= cn[w];
            }
        }
        uint64_t *t = CUR; CUR = NXT; NXT = t;
    }
    long long reached = 0;
    for (int v = 0; v < N; v++) {
        const uint64_t *cu = CUR + (size_t)v * W;
        for (int w = 0; w < W; w++) reached += pc64(cu[w]);
    }
    return (long long)N * N - reached;
}

/* Simulated annealing at the current order. Returns 1 when valid, 0 on timeout. */
static int anneal(void) {
    long long cost = eval();
    for (long it = 0;; it++) {
        if (cost == 0) return 1;
        if ((it & 7) == 0 && elapsed() >= budget) return 0;
        int e1 = rint_(EE), e2 = rint_(EE);
        if (e1 == e2) continue;
        int a1 = EA[e1], b1 = EB[e1], a2 = EA[e2], b2 = EB[e2];
        if (a1 == a2 || b1 == b2) continue;
        if (has_edge(a1, b2) || has_edge(a2, b1)) continue;
        sw(e1, e2);
        long long c = eval();
        long long delta = c - cost;
        double T = T0 * pow(T1 / T0, (double)(it % LSCHED) / LSCHED);
        if (delta <= 0 || rdbl() < exp(-(double)delta / T)) cost = c;
        else sw(e1, e2);
    }
}

/* Add one A-vertex and one B-vertex. Take d edges with distinct endpoints,
   reroute them through the two new vertices, so old degrees are unchanged. */
static int grow(int d) {
    if (NN + 2 > MAXN || EE + d > MAXE) return 0;
    int chosen[MAXD];
    int cnt = 0;
    stamp_++;
    for (int tries = 0; cnt < d && tries < 20000; tries++) {
        int e = rint_(EE);
        int x = EA[e], y = EB[e];
        if (usedA[x] == stamp_ || usedB[y] == stamp_) continue;
        usedA[x] = stamp_;
        usedB[y] = stamp_;
        chosen[cnt++] = e;
    }
    if (cnt < d) return 0;
    int na = NN, nb = NN + 1;
    DEGV[na] = 0;
    DEGV[nb] = 0;
    for (int i = 0; i < d; i++) {
        int e = chosen[i];
        int x = EA[e], y = EB[e];
        rep(x, y, nb);
        rep(y, x, na);
        EA[e] = na;                 /* edge e is now (na, y) */
        EA[EE + i] = x;             /* new edge is (x, nb)   */
        EB[EE + i] = nb;
        addn(na, y);
        addn(nb, x);
    }
    EE += d;
    NN += 2;
    return 1;
}

static void save(void) {
    bestN = NN;
    bestE = EE;
    have = 1;
    for (int e = 0; e < EE; e++) {
        BEA[e] = EA[e];
        BEB[e] = EB[e];
    }
}

static int setup(int n, int m, int d) {
    static int col[MAXN];
    static int dg[MAXN];
    static int q[MAXN];
    for (int v = 0; v < n; v++) dg[v] = 0;
    for (int e = 0; e < m; e++) {
        int u = SU[e], v = SV[e];
        if (u < 0 || v < 0 || u >= n || v >= n || u == v) return 0;
        if (++dg[u] > d || ++dg[v] > d) return 0;
    }
    for (int v = 0; v < n; v++) { DEGV[v] = 0; col[v] = -1; }
    for (int e = 0; e < m; e++) {
        int u = SU[e], v = SV[e];
        addn(u, v);
        addn(v, u);
    }
    for (int s = 0; s < n; s++) {
        if (col[s] != -1) continue;
        col[s] = 0;
        int h = 0, t = 0;
        q[t++] = s;
        while (h < t) {
            int u = q[h++];
            for (int i = 0; i < DEGV[u]; i++) {
                int w = ADJ[u * MAXD + i];
                if (col[w] == -1) { col[w] = 1 - col[u]; q[t++] = w; }
                else if (col[w] == col[u]) return 0;
            }
        }
    }
    for (int e = 0; e < m; e++) {
        int u = SU[e], v = SV[e];
        if (col[u] == 0) { EA[e] = u; EB[e] = v; }
        else { EA[e] = v; EB[e] = u; }
    }
    NN = n;
    EE = m;
    return 1;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed budget\n");
        return 1;
    }
    int d = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    budget = atof(argv[4]);
    tstart = clock();
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (rs == 0) rs = 1;
    for (int w = 0; w < 10; w++) rnext();

    int n0 = 0, m0 = 0;
    if (scanf("%d %d", &n0, &m0) != 2) { n0 = 0; m0 = 0; }
    if (n0 < 0 || m0 < 0 || m0 > MAXE || n0 > MAXN) { n0 = 0; m0 = 0; }
    int ok = 1;
    for (int e = 0; e < m0; e++) {
        if (scanf("%d %d", &SU[e], &SV[e]) != 2) { ok = 0; break; }
    }
    if (!ok) { n0 = 0; m0 = 0; }

    DEGD = d;
    if (n0 > 0 && d >= 1 && d <= MAXD && DIAM >= 1 && m0 >= 2) {
        if (setup(n0, m0, d)) {
            while (1) {
                if (!anneal()) break;
                save();
                if (!grow(d)) break;
            }
        }
    }

    if (have) {
        printf("%d %d\n", bestN, bestE);
        for (int e = 0; e < bestE; e++) printf("%d %d\n", BEA[e], BEB[e]);
    } else {
        printf("%d %d\n", n0, m0);
        for (int e = 0; e < m0; e++) printf("%d %d\n", SU[e], SV[e]);
    }
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

    # Known-optimal constructions cannot be beaten: return at once.
    if best_n >= lib.moore_bound(d, D):
        return best

    def left():
        return 0.88 * time_limit - (time.monotonic() - t0) - 1.5

    # Phase 1: lift search (a proven starting point).
    if left() >= 3.0:
        b1 = round(0.4 * left(), 2)
        try:
            out = lib.run_c(C_LIFT, [d, D, seed & 0xFFFFFFFF, b1],
                            stdin_graph=best, timeout=b1 + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    # Phase 2: free annealing with vertex-pair growth, from the best graph so far.
    if left() >= 3.0:
        b2 = round(left(), 2)
        try:
            out = lib.run_c(C_ANNEAL, [d, D, seed & 0xFFFFFFFF, b2],
                            stdin_graph=best, timeout=b2 + 3.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
