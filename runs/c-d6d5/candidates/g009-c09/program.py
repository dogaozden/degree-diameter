import itertools
import time

import lib


# ----------------------------------------------------------------------------
# New construction: voltage lifts with UNEQUAL bipartition.
#
# A base multigraph has KA A-vertices of degree a and KB B-vertices of degree b,
# with KA*a = KB*b (so the base is a biregular bipartite multigraph). Voltages
# live in a semidirect group H = Z_M x| Z_K2 of order G. Dart t = (i, j, s)
# joins A_i,g to B_j,g*s for all g in H. The lift has (KA+KB)*G vertices,
# A-vertices of degree a and B-vertices of degree b, both at most DEG.
#
# The earlier engine only used equal sides with a = b = DEG. Allowing shapes
# such as (a, b) = (6, 5) with KA = 5, KB = 6 gives orders (KA+KB)*G for
# different values of KA+KB, which reaches orders the equal-side family skips.
#
# Search: simulated annealing on the weighted count of uncovered (block, vertex)
# pairs, where block representatives are the vertices A_i,e and B_j,e. Left
# multiplication by H is an automorphism, so zero uncovered pairs for these
# representatives is equivalent to diameter <= D. Moves swap B-endpoints between
# two darts (this keeps B-degrees) or change a voltage. Breakout weights are
# raised on still-uncovered blocks. An elite pool gives iterated local search.
# ----------------------------------------------------------------------------

C_SOURCE = r"""
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <math.h>
#include <time.h>

#define BIGC 1000000000LL
#define MAXE 160
#define MAXSH 512
#define POOLMAX 40
#define POOLP 0.6
#define BRK 120
#define ITERS 5000
#define ILS_ITERS 2500

static uint64_t rs[2];
static struct timespec T0;
static double DEADLINE;

static uint64_t splitmix(uint64_t *x) {
    uint64_t z = (*x += 0x9E3779B97F4A7C15ULL);
    z = (z ^ (z >> 30)) * 0xBF58476D1CE4E5B9ULL;
    z = (z ^ (z >> 27)) * 0x94D049BB133111EBULL;
    return z ^ (z >> 31);
}

static uint64_t rnd64(void) {
    uint64_t s1 = rs[0];
    const uint64_t s0 = rs[1];
    rs[0] = s0;
    s1 ^= s1 << 23;
    rs[1] = s1 ^ s0 ^ (s1 >> 18) ^ (s0 >> 5);
    return rs[1] + s0;
}

static int rnd_int(int n) { return (int)(rnd64() % (uint64_t)n); }
static double rnd_unit(void) { return (double)(rnd64() >> 11) * (1.0 / 9007199254740992.0); }

static double elapsed(void) {
    struct timespec ts;
    timespec_get(&ts, TIME_UTC);
    return (double)(ts.tv_sec - T0.tv_sec) + 1e-9 * (double)(ts.tv_nsec - T0.tv_nsec);
}

static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(long long b, int e, int m) {
    long long r = 1 % m, x = b % m;
    while (e) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

static int DEG, DIAM;
static int AD, BD, KA, KB, KT, E, M, K2, R, G, NV;
static int *Rpow;
static int *dI, *dJ, *dS, *perm, *adj, *cnt, *stamp, *fr, *nx;
static int *bestJ, *bestS;
static int curstamp = 0;
static long long *wt = NULL, *unc = NULL;
static long long last_w = 0, wsum_w = 0;

static int best_n = 0, best_m = 0;
static int *best_e = NULL;

typedef struct { int a, b, ka, kb; } Shape;
static Shape shapes[MAXSH];
static int nshape = 0;

typedef struct {
    int a, b, ka, kb, M, K2, R, G;
    long long cost;
    int J[MAXE], S[MAXE];
} Cfg;
static Cfg pool[POOLMAX];
static int npool = 0;

/* (a,b)*(c,e) = (a + R^b c, b + e), element index a*K2 + b. */
static inline int gmul(int x, int y) {
    int a = x / K2, b = x % K2;
    int c = y / K2, e = y % K2;
    int ra = (int)(((long long)a + (long long)Rpow[b] * c) % M);
    int rb = (b + e) % K2;
    return ra * K2 + rb;
}

static void build_perm(int t) {
    int s = dS[t];
    int *pm = perm + (size_t)t * G;
    for (int g = 0; g < G; g++) pm[g] = gmul(g, s);
}

/* Returns the true cost (uncovered pairs summed over the KT block representatives).
   Sets unc[r] per block and last_w to the weighted cost. */
static long long eval_cost(void) {
    for (int t1 = 0; t1 < E; t1++)
        for (int t2 = t1 + 1; t2 < E; t2++)
            if (dI[t1] == dI[t2] && dJ[t1] == dJ[t2] && dS[t1] == dS[t2]) {
                for (int r = 0; r < KT; r++) unc[r] = 0;
                last_w = BIGC;
                return BIGC;
            }
    memset(cnt, 0, sizeof(int) * (size_t)NV);
    for (int t = 0; t < E; t++) {
        int ai = dI[t] * G, bj = (KA + dJ[t]) * G;
        const int *pm = perm + (size_t)t * G;
        for (int g = 0; g < G; g++) {
            int a = ai + g, b = bj + pm[g];
            adj[(size_t)a * DEG + cnt[a]++] = b;
            adj[(size_t)b * DEG + cnt[b]++] = a;
        }
    }
    long long total = 0, w = 0;
    for (int r = 0; r < KT; r++) {
        int src = r * G;
        if (curstamp >= 2000000000) {
            memset(stamp, 0, sizeof(int) * (size_t)NV);
            curstamp = 0;
        }
        curstamp++;
        int *f = fr, *h = nx;
        int fsz = 1, count = 1;
        f[0] = src;
        stamp[src] = curstamp;
        for (int lvl = 0; lvl < DIAM && fsz > 0; lvl++) {
            int nsz = 0;
            for (int q = 0; q < fsz; q++) {
                const int *au = adj + (size_t)f[q] * DEG;
                int dq = cnt[f[q]];
                for (int e = 0; e < dq; e++) {
                    int v = au[e];
                    if (stamp[v] != curstamp) {
                        stamp[v] = curstamp;
                        h[nsz++] = v;
                    }
                }
            }
            count += nsz;
            int *tmp = f; f = h; h = tmp;
            fsz = nsz;
        }
        unc[r] = NV - count;
        total += NV - count;
        w += wt[r] * unc[r];
    }
    last_w = w;
    return total;
}

static void setup_group(int sa, int sb, int ska, int skb, int m, int k2, int r, int g) {
    AD = sa; BD = sb; KA = ska; KB = skb; KT = ska + skb;
    E = ska * sa; M = m; K2 = k2; R = r; G = g; NV = KT * G;
    dI = malloc(sizeof(int) * (size_t)E);
    dJ = malloc(sizeof(int) * (size_t)E);
    dS = malloc(sizeof(int) * (size_t)E);
    bestJ = malloc(sizeof(int) * (size_t)E);
    bestS = malloc(sizeof(int) * (size_t)E);
    perm = malloc(sizeof(int) * (size_t)E * G);
    adj = malloc(sizeof(int) * (size_t)NV * DEG);
    cnt = malloc(sizeof(int) * (size_t)NV);
    stamp = calloc((size_t)NV, sizeof(int));
    fr = malloc(sizeof(int) * (size_t)NV);
    nx = malloc(sizeof(int) * (size_t)NV);
    Rpow = malloc(sizeof(int) * (size_t)K2);
    wt = malloc(sizeof(long long) * (size_t)KT);
    unc = malloc(sizeof(long long) * (size_t)KT);
    Rpow[0] = 1 % M;
    for (int p = 1; p < K2; p++) Rpow[p] = (int)((long long)Rpow[p - 1] * R % M);
    for (int t = 0; t < E; t++) dI[t] = t / AD;
    for (int r2 = 0; r2 < KT; r2++) wt[r2] = 1;
    wsum_w = KT;
    curstamp = 0;
}

static void free_config(void) {
    free(dI); free(dJ); free(dS); free(bestJ); free(bestS);
    free(perm); free(adj); free(cnt); free(stamp); free(fr); free(nx);
    free(Rpow); free(wt); free(unc);
    dI = dJ = dS = bestJ = bestS = perm = adj = cnt = stamp = fr = nx = Rpow = NULL;
    wt = unc = NULL;
}

static void emit(void) {
    long long ne = (long long)E * G;
    free(best_e);
    best_e = malloc(sizeof(int) * 2 * (size_t)ne);
    int idx = 0;
    for (int t = 0; t < E; t++)
        for (int g = 0; g < G; g++) {
            best_e[idx++] = dI[t] * G + g;
            best_e[idx++] = (KA + dJ[t]) * G + perm[(size_t)t * G + g];
        }
    best_m = (int)ne;
    best_n = NV;
}

/* Random biregular base: B-degrees are BD each, A-degrees are AD each (fixed by dI). */
static void random_init(void) {
    for (int t = 0; t < E; t++) dJ[t] = t / BD;
    for (int i = E - 1; i > 0; i--) {
        int j = rnd_int(i + 1);
        int tmp = dJ[i]; dJ[i] = dJ[j]; dJ[j] = tmp;
    }
    for (int t = 0; t < E; t++) {
        dS[t] = rnd_int(G);
        build_perm(t);
    }
}

static void perturb(int nmoves) {
    for (int s = 0; s < nmoves; s++) {
        if (rnd_unit() < 0.3) {
            int t1 = rnd_int(E), t2 = rnd_int(E);
            if (t1 == t2 || dJ[t1] == dJ[t2]) continue;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
        } else {
            int t = rnd_int(E);
            dS[t] = rnd_int(G);
            build_perm(t);
        }
    }
}

static long long run_sa(int iters, double tscale, long long cost) {
    long long bestc = cost, wcur = last_w, prevc = cost;
    memcpy(bestJ, dJ, sizeof(int) * (size_t)E);
    memcpy(bestS, dS, sizeof(int) * (size_t)E);
    for (int it = 0; it < iters && bestc > 0; it++) {
        if ((it & 63) == 0 && elapsed() > DEADLINE) break;
        if (it > 0 && it % BRK == 0) {
            if (cost < BIGC && cost >= prevc) {
                eval_cost();
                for (int r = 0; r < KT; r++)
                    if (unc[r] > 0) { wt[r]++; wsum_w++; }
                wcur = 0;
                for (int r = 0; r < KT; r++) wcur += wt[r] * unc[r];
            }
            prevc = cost;
        }
        double sc = (double)wsum_w / (double)KT;
        double temp = tscale * (3.0 * (1.0 - (double)it / iters) + 0.05) * sc;
        if (rnd_unit() < 0.3) {
            int t1 = rnd_int(E), t2 = rnd_int(E);
            if (t1 == t2 || dJ[t1] == dJ[t2]) continue;
            int tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2; wcur = w2;
            } else {
                tmp = dJ[t1]; dJ[t1] = dJ[t2]; dJ[t2] = tmp;
            }
        } else {
            int t = rnd_int(E);
            int olds = dS[t];
            int news = rnd_int(G);
            if (news == olds) continue;
            dS[t] = news;
            build_perm(t);
            long long c2 = eval_cost();
            long long w2 = last_w;
            if (w2 <= wcur || rnd_unit() < exp(-(double)(w2 - wcur) / temp)) {
                cost = c2; wcur = w2;
            } else {
                dS[t] = olds;
                build_perm(t);
            }
        }
        if (cost < bestc) {
            bestc = cost;
            memcpy(bestJ, dJ, sizeof(int) * (size_t)E);
            memcpy(bestS, dS, sizeof(int) * (size_t)E);
        }
    }
    return bestc;
}

static void finish_run(long long bc) {
    if (bc == 0) {
        memcpy(dJ, bestJ, sizeof(int) * (size_t)E);
        memcpy(dS, bestS, sizeof(int) * (size_t)E);
        for (int t = 0; t < E; t++) build_perm(t);
        if (NV > best_n) emit();
    }
}

static void pool_add(long long cost, int a, int b, int ka, int kb, int m, int k2, int r, int g,
                     const int *J, const int *S) {
    if (cost <= 0 || cost >= BIGC) return;
    int slot;
    if (npool < POOLMAX) {
        slot = npool++;
    } else {
        slot = 0;
        for (int i = 1; i < POOLMAX; i++)
            if (pool[i].cost > pool[slot].cost) slot = i;
        if (pool[slot].cost <= cost) return;
    }
    Cfg *c = &pool[slot];
    int ee = ka * a;
    c->a = a; c->b = b; c->ka = ka; c->kb = kb;
    c->M = m; c->K2 = k2; c->R = r; c->G = g; c->cost = cost;
    memcpy(c->J, J, sizeof(int) * (size_t)ee);
    memcpy(c->S, S, sizeof(int) * (size_t)ee);
}

static int pick_pool(void) {
    int cand[POOLMAX], nc = 0;
    for (int i = 0; i < npool; i++) {
        long long nn = (long long)(pool[i].ka + pool[i].kb) * pool[i].G;
        if (nn > best_n) cand[nc++] = i;
    }
    if (nc == 0) return -1;
    int bi = cand[rnd_int(nc)];
    for (int s = 0; s < 2; s++) {
        int c = cand[rnd_int(nc)];
        if (pool[c].cost < pool[bi].cost) bi = c;
    }
    return bi;
}

int main(int argc, char **argv) {
    if (argc < 5) {
        fprintf(stderr, "usage: prog d D seed time_limit [start_n]\n");
        return 1;
    }
    timespec_get(&T0, TIME_UTC);
    DEG = atoi(argv[1]);
    DIAM = atoi(argv[2]);
    uint64_t sd = strtoull(argv[3], NULL, 10);
    DEADLINE = atof(argv[4]);
    int start_n = argc > 5 ? atoi(argv[5]) : 0;
    best_n = start_n;
    best_m = 0;
    if (DEG < 1 || DIAM < 1) {
        printf("0 0\n");
        return 0;
    }
    /* Base shapes: KA*a = KB*b with a, b <= DEG. */
    for (int a = 1; a <= DEG; a++)
        for (int b = 1; b <= DEG; b++)
            for (int t = 1; t <= 2; t++) {
                int g = gcd_i(a, b);
                int ka = t * b / g, kb = t * a / g;
                if (ka * a <= MAXE && nshape < MAXSH) {
                    shapes[nshape].a = a;
                    shapes[nshape].b = b;
                    shapes[nshape].ka = ka;
                    shapes[nshape].kb = kb;
                    nshape++;
                }
            }
    uint64_t sm = sd * 2654435761ULL + 987654321ULL;
    rs[0] = splitmix(&sm);
    rs[1] = splitmix(&sm);

    while (elapsed() < DEADLINE) {
        int pi = -1;
        if (npool > 0 && rnd_unit() < POOLP) pi = pick_pool();
        if (pi >= 0) {
            Cfg c = pool[pi];
            setup_group(c.a, c.b, c.ka, c.kb, c.M, c.K2, c.R, c.G);
            memcpy(dJ, c.J, sizeof(int) * (size_t)E);
            memcpy(dS, c.S, sizeof(int) * (size_t)E);
            for (int t = 0; t < E; t++) build_perm(t);
            perturb(2 + rnd_int(4));
            long long cst = eval_cost();
            long long bc = run_sa(ILS_ITERS, 0.35, cst);
            finish_run(bc);
            pool_add(bc, c.a, c.b, c.ka, c.kb, c.M, c.K2, c.R, c.G, bestJ, bestS);
            free_config();
            continue;
        }

        Shape s = shapes[rnd_int(nshape)];
        int kt = s.ka + s.kb;
        int gmin = best_n / kt + 1;
        int spread = gmin / 6 + 2;
        int g = gmin + rnd_int(spread);
        if (g < 2) g = 2;
        int opts[32], no = 0;
        for (int c = 1; c <= 12 && c <= g; c++)
            if (g % c == 0 && g / c >= 2) opts[no++] = c;
        int k2 = opts[rnd_int(no)];
        int m = g / k2, r = 1;
        if (k2 > 1) {
            int found = 0;
            for (int tr = 0; tr < 200 && !found; tr++) {
                int cand = 1 + rnd_int(m - 1);
                if (gcd_i(cand, m) == 1 && powmod(cand, k2, m) == 1 % m) {
                    r = cand;
                    found = 1;
                }
            }
            if (!found) {
                k2 = 1;
                m = g;
                r = 1;
            }
        }
        setup_group(s.a, s.b, s.ka, s.kb, m, k2, r, g);
        random_init();
        long long cost = eval_cost();
        long long bc = run_sa(ITERS, 1.0, cost);
        finish_run(bc);
        pool_add(bc, s.a, s.b, s.ka, s.kb, m, k2, r, g, bestJ, bestS);
        free_config();
    }

    if (best_m > 0) {
        printf("%d %d\n", best_n, best_m);
        for (int i = 0; i < best_m; i++)
            printf("%d %d\n", best_e[2 * i], best_e[2 * i + 1]);
    } else {
        printf("0 0\n");
    }
    return 0;
}
"""


# ----------------------------------------------------------------------------
# Safe baseline families (always valid fallbacks).
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
# Driver: baselines in Python, then the C search over unequal-sided lifts.
# ----------------------------------------------------------------------------

def build(d, D, seed, time_limit):
    start = time.monotonic()
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

    if D >= 4 and time.monotonic() - start < 0.3 * time_limit:
        gq = _best_gq(d)
        if gq is not None:
            consider(gq[0], gq[1])

    if best_n >= lib.moore_bound(d, D):
        return best

    # Leave margin for compilation (counted from process start), parsing and validation.
    remaining = 0.88 * time_limit - (time.monotonic() - start) - 2.0
    if remaining >= 1.0:
        try:
            out = lib.run_c(C_SOURCE, [d, D, seed, f"{remaining:.2f}", best_n],
                            timeout=remaining + 4.0)
            n, e = lib.parse_graph_text(out)
            consider(n, e)
        except Exception:
            pass

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
