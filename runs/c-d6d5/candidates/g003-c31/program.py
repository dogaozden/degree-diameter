import itertools
import time

import lib


# Stage 1: voltage-lift simulated annealing over semidirect products (proven engine).
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


# Stage 2: bitset-based annealing on general bipartite graphs. The graph is
# kept bipartite (A = lower half, B = upper half) with max degree d. Moves are
# degree-preserving edge switches and additions between deficient vertices.
# Cost = number of unordered pairs at distance > D. When cost reaches 0 the
# graph is valid, so it is saved and grown by one A and one B vertex.
C_ANNEAL = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define MAXN 1400
#define MAXW ((MAXN + 63) / 64)
#define MAXDEG 16
#define MAXE (MAXN * MAXDEG / 2 + 64)
#define STAGE_EVALS 12000

static int DEG, DIAM, N, W, E;
static int COL[MAXN];
static unsigned char ADJ[MAXN][MAXN];
static int NB[MAXN][MAXDEG];
static int DG[MAXN];
static int EA[MAXE], EB[MAXE];
static int BEA[MAXE], BEB[MAXE], bestN, bestE;
static int IU[MAXE], IV[MAXE];
static int LA[MAXN], LB[MAXN];
static uint64_t RA[MAXN * MAXW], RB[MAXN * MAXW];
static unsigned long long rs = 88172645463325252ULL;
static clock_t t0c;

static unsigned long long rnext(void) {
    rs ^= rs << 13;
    rs ^= rs >> 7;
    rs ^= rs << 17;
    return rs;
}
static int rint_(int n) { return (int)(rnext() % (unsigned long long)n); }
static double rdbl(void) { return (double)(rnext() >> 11) * (1.0 / 9007199254740992.0); }
static double elapsed(void) { return (double)(clock() - t0c) / CLOCKS_PER_SEC; }

static int pc64(uint64_t x) {
    x = x - ((x >> 1) & 0x5555555555555555ULL);
    x = (x & 0x3333333333333333ULL) + ((x >> 2) & 0x3333333333333333ULL);
    x = (x + (x >> 4)) & 0x0F0F0F0F0F0F0F0FULL;
    return (int)((x * 0x0101010101010101ULL) >> 56);
}

static void unlink_nb(int v, int x) {
    for (int k = 0; k < DG[v]; k++)
        if (NB[v][k] == x) { NB[v][k] = NB[v][--DG[v]]; return; }
}

static void rep_nb(int v, int old, int nw) {
    for (int k = 0; k < DG[v]; k++)
        if (NB[v][k] == old) { NB[v][k] = nw; return; }
}

static void add_edge(int a, int b) {
    ADJ[a][b] = 1; ADJ[b][a] = 1;
    NB[a][DG[a]++] = b;
    NB[b][DG[b]++] = a;
    EA[E] = a; EB[E] = b; E++;
}

static void pop_edge(void) {
    E--;
    int a = EA[E], b = EB[E];
    ADJ[a][b] = 0; ADJ[b][a] = 0;
    unlink_nb(a, b);
    unlink_nb(b, a);
}

/* Replace edges (a,b),(a2,b2) by (a,b2),(a2,b). Applying it twice restores. */
static void swapB(int i, int j) {
    int a = EA[i], b = EB[i], a2 = EA[j], b2 = EB[j];
    ADJ[a][b] = 0; ADJ[b][a] = 0;
    ADJ[a2][b2] = 0; ADJ[b2][a2] = 0;
    ADJ[a][b2] = 1; ADJ[b2][a] = 1;
    ADJ[a2][b] = 1; ADJ[b][a2] = 1;
    rep_nb(a, b, b2);
    rep_nb(b, a, a2);
    rep_nb(a2, b2, b);
    rep_nb(b2, a2, a);
    EB[i] = b2;
    EB[j] = b;
}

static void clear_graph(void) {
    for (int i = 0; i < MAXN; i++) {
        memset(ADJ[i], 0, MAXN);
        DG[i] = 0;
    }
    E = 0;
}

static void save_best(void) {
    bestN = N;
    bestE = E;
    memcpy(BEA, EA, sizeof(int) * E);
    memcpy(BEB, EB, sizeof(int) * E);
}

static void load_best(void) {
    clear_graph();
    N = bestN;
    W = (N + 63) / 64;
    for (int i = 0; i < bestE; i++) add_edge(BEA[i], BEB[i]);
}

static int grow(void) {
    if (N + 2 > MAXN) return 0;
    int a = N, b = N + 1;
    COL[a] = 0; COL[b] = 1;
    DG[a] = 0; DG[b] = 0;
    N += 2;
    W = (N + 63) / 64;
    return 1;
}

/* Number of unordered pairs at distance > DIAM. */
static long long evalcost(void) {
    int n = N, w = W;
    uint64_t *cur = RA, *nxt = RB;
    for (int v = 0; v < n; v++) {
        uint64_t *row = cur + v * w;
        for (int k = 0; k < w; k++) row[k] = 0;
        row[v >> 6] |= 1ULL << (v & 63);
    }
    for (int r = 0; r < DIAM; r++) {
        for (int v = 0; v < n; v++) {
            uint64_t *dst = nxt + v * w;
            memcpy(dst, cur + v * w, sizeof(uint64_t) * (size_t)w);
            for (int k = 0; k < DG[v]; k++) {
                const uint64_t *src = cur + NB[v][k] * w;
                for (int t = 0; t < w; t++) dst[t] |= src[t];
            }
        }
        uint64_t *tmp = cur; cur = nxt; nxt = tmp;
    }
    long long tot = 0;
    for (int i = 0; i < n * w; i++) tot += pc64(cur[i]);
    return ((long long)n * n - tot) / 2;
}

static void emit(int n, int m, const int *A, const int *B) {
    printf("%d %d\n", n, m);
    for (int i = 0; i < m; i++) printf("%d %d\n", A[i], B[i]);
}

int main(int argc, char **argv) {
    if (argc < 5) return 1;
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    unsigned long long seed = strtoull(argv[3], NULL, 10);
    double budget = atof(argv[4]);
    t0c = clock();
    rs ^= (seed + 1ULL) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int w = 0; w < 10; w++) rnext();

    int sn = 0, sm = 0;
    if (scanf("%d %d", &sn, &sm) != 2 || sn < 2 || sm < 0 || sm > MAXE ||
        sn > MAXN || (sn & 1) || DEG < 1 || DEG > MAXDEG || DIAM < 2) {
        printf("2 1\n0 1\n");
        return 0;
    }
    for (int e = 0; e < sm; e++)
        if (scanf("%d %d", &IU[e], &IV[e]) != 2) { printf("2 1\n0 1\n"); return 0; }

    int h = sn / 2;
    for (int v = 0; v < sn; v++) COL[v] = (v >= h) ? 1 : 0;
    clear_graph();
    N = sn;
    W = (N + 63) / 64;
    int ok = 1;
    for (int e = 0; e < sm && ok; e++) {
        int u = IU[e], v = IV[e];
        if (u < 0 || v < 0 || u >= sn || v >= sn || (u < h) == (v < h)) { ok = 0; break; }
        int a = (u < h) ? u : v;
        int b = (u < h) ? v : u;
        if (DG[a] >= DEG || DG[b] >= DEG || ADJ[a][b]) { ok = 0; break; }
        add_edge(a, b);
    }
    if (!ok) {
        emit(sn, sm, IU, IV);
        return 0;
    }

    save_best();
    long long cost = evalcost();
    int stage = 0;

    while (elapsed() < budget) {
        if (cost == 0) {
            if (N > bestN) save_best();
            if (!grow()) break;
            cost = evalcost();
            stage = 0;
            continue;
        }
        if (stage >= STAGE_EVALS) {
            load_best();
            if (!grow()) break;
            cost = evalcost();
            stage = 0;
            continue;
        }
        stage++;
        double T = 2.0 * pow(0.03, (double)stage / STAGE_EVALS);
        if (rdbl() < 0.3) {
            int na = 0, nb = 0;
            for (int v = 0; v < N; v++) {
                if (DG[v] < DEG) {
                    if (COL[v] == 0) LA[na++] = v;
                    else LB[nb++] = v;
                }
            }
            if (na == 0 || nb == 0) continue;
            int a = -1, b = -1;
            for (int t = 0; t < 30; t++) {
                int x = LA[rint_(na)], y = LB[rint_(nb)];
                if (!ADJ[x][y]) { a = x; b = y; break; }
            }
            if (a < 0) continue;
            add_edge(a, b);
            long long nc = evalcost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else pop_edge();
        } else {
            if (E < 2) continue;
            int i = rint_(E), j = rint_(E);
            if (i == j) continue;
            if (ADJ[EA[i]][EB[j]] || ADJ[EA[j]][EB[i]]) continue;
            swapB(i, j);
            long long nc = evalcost();
            if (nc <= cost || rdbl() < exp(-(double)(nc - cost) / T)) cost = nc;
            else swapB(i, j);
        }
    }

    emit(bestN, bestE, BEA, BEB);
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

    def spent():
        return time.monotonic() - t0

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

    if D >= 4 and spent() < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    # Already at the Moore bound: nothing to gain.
    if best_n >= lib.moore_bound(d, D):
        return best

    seed32 = seed & 0xFFFFFFFF

    # Stage 1: lift search gives a strong starting graph.
    b1 = 0.30 * time_limit - spent()
    if b1 >= 2.0:
        try:
            out = lib.run_c(C_LIFT, [d, D, seed32, round(b1, 2)],
                            stdin_graph=best, timeout=b1 + 6.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    # Stage 2: bitset annealing grows the stage-1 graph by vertex pairs.
    b2 = 0.85 * time_limit - spent() - 3.0
    if b2 >= 2.0:
        try:
            out = lib.run_c(C_ANNEAL, [d, D, seed32, round(b2, 2)],
                            stdin_graph=best, timeout=b2 + 6.0)
            consider(*lib.parse_graph_text(out))
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
