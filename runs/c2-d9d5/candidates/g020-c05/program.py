"""Block voltage lifts over affine groups for the bipartite degree-diameter problem.

Change in this version: the parent searched only Haar graphs (one base vertex per
side). This version searches a different family. The base graph has k left and k
right vertices with circulant multiplicities c_0..c_{k-1} (sum = d). Each base dart
(u, v) carries a voltage w in G = F_p x| C_c (p prime, c | p-1). Vertices are
(u, g) on the left and (v, h) on the right, and (u, g) ~ (v, g*w) for every dart.
The lift is d-regular, bipartite and simple (voltages are distinct within each base
pair). Left multiplication by G is an automorphism, so the diameter test reduces to
2k BFS runs, one from each base vertex's identity element.

Search: simulated annealing over the voltages for each configuration, with a binary
search over group orders and time slices per probe. The first C run uses k = 2, 3
(new family). The second run uses k = 1, which is the parent's Haar family on prime
groups, and acts as a fallback that must beat the first result. Every returned
graph is checked with lib.is_valid, and the K_{d,d} / projective-plane / Araujo-Lopez
baselines remain as fallbacks.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Block voltage lift search over affine groups F_p x| C_c.
 * Usage: prog d D seed time_limit lo hi kmin kmax     (stdin ignored)
 * Output: "n m" then m lines "u v" for the best valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXM 8192
#define MAXK 3
#define MAXD 32
#define MAXDART (MAXK * MAXD)
#define MAXV (2 * MAXK * MAXM)
#define MAXCAND 20000
#define MAXCFG 8
#define ITERS 2000

typedef struct { int k; int c[MAXK]; } Cfg;
typedef struct { int p, c, M; } Grp;

static int d, DD;
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

/* ------------------------------------------------------------ number theory */

static long long powmod(long long b, long long e, long long m) {
    long long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
}

static int is_prime_int(int n) {
    if (n < 2) return 0;
    for (int f = 2; f * f <= n; f++)
        if (n % f == 0) return 0;
    return 1;
}

static int primroot(int p) {
    if (p == 2) return 1;
    int fac[32], nf = 0, n = p - 1;
    for (int f = 2; f * f <= n; f++) {
        if (n % f == 0) {
            fac[nf++] = f;
            while (n % f == 0) n /= f;
        }
    }
    if (n > 1) fac[nf++] = n;
    for (int g = 2; g < p; g++) {
        int ok = 1;
        for (int i = 0; i < nf && ok; i++)
            if (powmod(g, (p - 1) / fac[i], p) == 1) ok = 0;
        if (ok) return g;
    }
    return -1;
}

/* ------------------------------------------------------------ group G = F_p x| C_c */

/* Element (a, j) is coded a*c + j and means (a, h_j), where h_j = pr^(j*(p-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_{j+t}).                              */
static int G_p, G_c, G_M;
static int Hel[MAXM];

static void setup_group(int p, int c) {
    G_p = p;
    G_c = c;
    G_M = p * c;
    int pr = primroot(p);
    int s = (p - 1) / c;
    for (int j = 0; j < c; j++) Hel[j] = (int)powmod(pr, (long long)j * s, p);
}

static inline int gmul(int x, int y) {
    int a = x / G_c, j = x - a * G_c;
    int b = y / G_c, t = y - b * G_c;
    int na = (int)(((long long)Hel[j] * b + a) % G_p);
    int nj = j + t;
    if (nj >= G_c) nj -= G_c;
    return na * G_c + nj;
}

static int ginv(int x) {
    int a = x / G_c, j = x - a * G_c;
    int y = (G_c - j) % G_c;
    int na = (int)((G_p - ((long long)Hel[y] * a) % G_p) % G_p);
    return na * G_c + y;
}

static Grp groups[MAXCAND];
static int ngroups = 0;

static int cmp_grp(const void *a, const void *b) {
    const Grp *x = (const Grp *)a, *y = (const Grp *)b;
    return (x->M > y->M) - (x->M < y->M);
}

static void build_groups(void) {
    for (int p = 3; p <= MAXM; p++) {
        if (!is_prime_int(p)) continue;
        for (int c = 1; c <= p - 1 && (long)p * c <= MAXM; c++) {
            if ((p - 1) % c) continue;
            if (ngroups < MAXCAND) {
                groups[ngroups].p = p;
                groups[ngroups].c = c;
                groups[ngroups].M = p * c;
                ngroups++;
            }
        }
    }
    qsort(groups, (size_t)ngroups, sizeof(Grp), cmp_grp);
}

/* ------------------------------------------------------------ block configurations */

static Cfg cfgs[MAXCFG];
static int ncfg = 0;

static void build_cfgs(int kmin, int kmax) {
    ncfg = 0;
    if (kmin <= 1 && 1 <= kmax) {
        Cfg x;
        x.k = 1;
        x.c[0] = d;
        x.c[1] = 0;
        x.c[2] = 0;
        cfgs[ncfg++] = x;
    }
    if (kmin <= 2 && 2 <= kmax) {
        int cnt = 0;
        for (int a = d / 2; a >= 1 && cnt < 2 && ncfg < MAXCFG; a--) {
            if (d - a < 1) continue;
            Cfg x;
            x.k = 2;
            x.c[0] = a;
            x.c[1] = d - a;
            x.c[2] = 0;
            cfgs[ncfg++] = x;
            cnt++;
        }
    }
    if (kmin <= 3 && 3 <= kmax) {
        Cfg tri[256];
        int score[256], used[256], ntri = 0;
        for (int a = 1; a <= d; a++)
            for (int b = a; b <= d; b++) {
                int c = d - a - b;
                if (c < b || ntri >= 256) continue;
                Cfg x;
                x.k = 3;
                x.c[0] = a;
                x.c[1] = b;
                x.c[2] = c;
                tri[ntri] = x;
                score[ntri] = a * a + b * b + c * c;
                used[ntri] = 0;
                ntri++;
            }
        int cnt = 0;
        while (cnt < 2 && ncfg < MAXCFG) {
            int best = -1;
            for (int i = 0; i < ntri; i++)
                if (!used[i] && (best < 0 || score[i] < score[best])) best = i;
            if (best < 0) break;
            used[best] = 1;
            cfgs[ncfg++] = tri[best];
            cnt++;
        }
    }
}

/* ------------------------------------------------------------ lift state */

static int CK;
static int nd, dU[MAXDART], dV[MAXDART];
static int ldeg[MAXK], rdeg[MAXK];
static int ldart[MAXK][MAXD], rdart[MAXK][MAXD];
static int W[MAXDART], Winv[MAXDART];
static int fwdT[MAXDART][MAXM], bwdT[MAXDART][MAXM];
static int stampv[MAXV], que[MAXV];
static int stamp = 0;

static void build_darts(const Cfg *cf) {
    int k = cf->k;
    CK = k;
    nd = 0;
    for (int u = 0; u < k; u++)
        for (int v = 0; v < k; v++) {
            int m = cf->c[((v - u) % k + k) % k];
            for (int t = 0; t < m; t++) {
                dU[nd] = u;
                dV[nd] = v;
                nd++;
            }
        }
    for (int u = 0; u < k; u++) {
        ldeg[u] = 0;
        rdeg[u] = 0;
    }
    for (int j = 0; j < nd; j++) {
        int u = dU[j], v = dV[j];
        ldart[u][ldeg[u]++] = j;
        rdart[v][rdeg[v]++] = j;
    }
}

static void refresh(int j) {
    Winv[j] = ginv(W[j]);
    for (int g = 0; g < G_M; g++) {
        fwdT[j][g] = gmul(g, W[j]);
        bwdT[j][g] = gmul(g, Winv[j]);
    }
}

/* True if voltage x clashes with an earlier dart (index < lim) on the same base pair. */
static int conflict(int j, int x, int lim) {
    for (int i = 0; i < lim; i++)
        if (i != j && dU[i] == dU[j] && dV[i] == dV[j] && W[i] == x) return 1;
    return 0;
}

static void random_init(void) {
    for (int j = 0; j < nd; j++) {
        int x;
        do { x = rndint(G_M); } while (conflict(j, x, j));
        W[j] = x;
        refresh(j);
    }
}

/* Vertices: left (u, g) = u*M + g; right (v, h) = (CK + v)*M + h.
 * Edge (u, g) ~ (v, g*W_j) for each dart j = (u, v). Left-multiplication is an
 * automorphism, so BFS from (u, e) for every base vertex decides the diameter.   */
static int DDdummy = 0;

static int bfs_reach(int src) {
    int M = G_M, KM = CK * M;
    stamp++;
    int head = 0, tail = 0;
    que[tail++] = src;
    stampv[src] = stamp;
    for (int lvl = 0; lvl < DD && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int x = que[head++];
            if (x < KM) {
                int u = x / M, g = x - u * M;
                for (int i = 0; i < ldeg[u]; i++) {
                    int j = ldart[u][i];
                    int y = (CK + dV[j]) * M + fwdT[j][g];
                    if (stampv[y] != stamp) {
                        stampv[y] = stamp;
                        que[tail++] = y;
                    }
                }
            } else {
                int r = x - KM, v = r / M, h = r - v * M;
                for (int i = 0; i < rdeg[v]; i++) {
                    int j = rdart[v][i];
                    int y = dU[j] * M + bwdT[j][h];
                    if (stampv[y] != stamp) {
                        stampv[y] = stamp;
                        que[tail++] = y;
                    }
                }
            }
        }
    }
    return tail;
}

static long cover_cost(void) {
    long tot = 0;
    int VC = 2 * CK * G_M;
    for (int u = 0; u < CK; u++) tot += VC - bfs_reach(u * G_M);
    for (int v = 0; v < CK; v++) tot += VC - bfs_reach((CK + v) * G_M);
    return tot;
}

/* Simulated annealing over voltages. Returns 1 at cost 0, 0 on timeout. */
static int anneal(double until) {
    while (now() < until) {
        random_init();
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int j = rndint(nd);
            int x;
            do { x = rndint(G_M); } while (conflict(j, x, nd));
            int old = W[j];
            W[j] = x;
            refresh(j);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                W[j] = old;
                refresh(j);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ best result */

static int lo_g, hi_g;
static int bestFound = 0, bestTotal = 0, bestP, bestC;
static Cfg bestCfg;
static int bestW[MAXDART];

static void record(const Cfg *cf) {
    int total = 2 * CK * G_M;
    if (total < lo_g || total > hi_g) return;
    if (bestFound && total <= bestTotal) return;
    bestFound = 1;
    bestTotal = total;
    bestP = G_p;
    bestC = G_c;
    bestCfg = *cf;
    for (int j = 0; j < nd; j++) bestW[j] = W[j];
}

static void run_cfg(const Cfg *cf, double until) {
    int k = cf->k;
    long Mlo = ((long)lo_g + 2 * k - 1) / (2 * k);
    long Mhi = (long)hi_g / (2 * k);
    if (Mhi > MAXM) Mhi = MAXM;
    if (Mlo < 3) Mlo = 3;
    int ia = -1, ib = -1;
    for (int i = 0; i < ngroups; i++) {
        if (groups[i].M >= Mlo && ia < 0) ia = i;
        if (groups[i].M <= Mhi) ib = i;
    }
    if (ia < 0 || ib < 0 || ia > ib) return;
    build_darts(cf);
    int a = ia, b = ib;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        int span = b - a + 1, probes = 1;
        while (span > 1) {
            span = (span + 1) / 2;
            probes++;
        }
        double rem = until - now();
        double slice = rem / (probes + 1);
        if (slice < 0.5) slice = 0.5;
        if (slice > rem) slice = rem;
        setup_group(groups[mid].p, groups[mid].c);
        if (anneal(now() + slice)) {
            record(cf);
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
}

static void print_best(void) {
    int k = bestCfg.k;
    setup_group(bestP, bestC);
    build_darts(&bestCfg);
    for (int j = 0; j < nd; j++) W[j] = bestW[j];
    int M = G_M;
    printf("%d %d\n", 2 * k * M, nd * M);
    for (int j = 0; j < nd; j++) {
        int u = dU[j], v = dV[j];
        for (int g = 0; g < M; g++) {
            printf("%d %d\n", u * M + g, (k + v) * M + gmul(g, W[j]));
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    DD = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    lo_g = atoi(argv[5]);
    hi_g = atoi(argv[6]);
    int kmin = atoi(argv[7]), kmax = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.92 - 0.3;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();
    (void)DDdummy;

    if (d < 2 || d > MAXD || DD < 2) {
        printf("0 0\n");
        return 0;
    }
    if (lo_g < 1) lo_g = 1;
    if (hi_g > 2 * MAXK * MAXM) hi_g = 2 * MAXK * MAXM;

    build_groups();
    build_cfgs(kmin, kmax);

    for (int ci = 0; ci < ncfg; ci++) {
        double rem = t_end - now();
        if (rem <= 0.2) break;
        double share = rem / (ncfg - ci);
        run_cfg(&cfgs[ci], now() + share);
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

    def remaining():
        return time_limit * 0.85 - (time.monotonic() - t0) - 3.0

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

    # Block voltage lifts (new family), then the Haar-type k = 1 family as a second chance.
    if 2 <= d <= 32 and D >= 3:
        mb = min(lib.moore_bound(d, D), 10 ** 8)
        for kmin, kmax, share in ((2, 3, 0.6), (1, 1, 1.0)):
            avail = remaining()
            if avail < 4.0:
                break
            budget = avail * share
            lo_total = best[0] + 1
            if lo_total > mb:
                break
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo_total, mb, kmin, kmax],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the best valid graph found so far

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
