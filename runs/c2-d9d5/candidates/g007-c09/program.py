"""Voltage lifts over small non-abelian groups for the bipartite degree-diameter problem.

Change from the parent: the C engine no longer searches only Haar graphs (one
base vertex per side, d parallel darts) over affine groups. It searches
s x s base multigraphs (s = 1, 2, 3) that are unions of d random perfect
matchings, lifted with voltages in a group G. The group is either the affine
group F_q x| H or the metacyclic group Z_m x| Z_k (r^k = 1 mod m, r = 1 gives
the direct product). The lift has 2sn vertices, is bipartite and d-regular,
and the group acts by left translation, so each base vertex gives one BFS
source. Diameter <= D is therefore checked with 2s BFS runs. Voltages are
annealed, and each probe restarts on a random group and base pattern.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines.
The C order search is a binary search over orders in steps of 12, then a
small upward sweep. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Lift search over affine and metacyclic groups with s x s base multigraphs.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * Output: "V E" then E lines "u v" for the largest valid graph found, or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXQ 256
#define MAXC 256
#define MAXD 40
#define MAXS 3
#define MAXN 3000
#define MAXV (2 * MAXS * MAXN)
#define MAXT (2 * MAXN)
#define ITERS 5000

typedef struct { int fam, n, m, k, r, q, p, kf, c; } Grp;

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
static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

/* ------------------------------------------------------------ finite fields */

static int ADDT[MAXQ][MAXQ], MULT[MAXQ][MAXQ], NEGT[MAXQ];
static int built_q = -1;

static int factor_pp(int q, int *p, int *k) {
    int pp = 0;
    for (int f = 2; f * f <= q; f++)
        if (q % f == 0) { pp = f; break; }
    if (!pp) pp = q;
    int r = q, kk = 0;
    while (r % pp == 0) { r /= pp; kk++; }
    if (r != 1 || kk < 1) return 0;
    *p = pp;
    *k = kk;
    return 1;
}

static int polymul(int a, int b, int p, int k, const int *pw, const int *m) {
    int pa[16], pb[16], prod[32];
    for (int i = 0; i < k; i++) {
        pa[i] = (a / pw[i]) % p;
        pb[i] = (b / pw[i]) % p;
    }
    for (int i = 0; i < 2 * k; i++) prod[i] = 0;
    for (int i = 0; i < k; i++)
        for (int j = 0; j < k; j++)
            prod[i + j] = (prod[i + j] + pa[i] * pb[j]) % p;
    for (int deg = 2 * k - 2; deg >= k; deg--) {
        int c = prod[deg];
        if (!c) continue;
        for (int i = 0; i < k; i++) {
            int idx = deg - k + i;
            prod[idx] = ((prod[idx] - c * m[i]) % p + p) % p;
        }
        prod[deg] = 0;
    }
    int r = 0;
    for (int i = 0; i < k; i++) r += prod[i] * pw[i];
    return r;
}

static void build_field(int q, int p, int k) {
    if (built_q == q) return;
    int pw[16];
    pw[0] = 1;
    for (int i = 1; i <= k; i++) pw[i] = pw[i - 1] * p;
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++) {
            int r = 0;
            for (int i = 0; i < k; i++)
                r += (((a / pw[i]) % p + (b / pw[i]) % p) % p) * pw[i];
            ADDT[a][b] = r;
        }
    for (int a = 0; a < q; a++)
        for (int b = 0; b < q; b++)
            if (ADDT[a][b] == 0) NEGT[a] = b;

    int found = 0;
    for (int code = 0; code < q && !found; code++) {
        int m[16];
        int t = code;
        for (int i = 0; i < k; i++) { m[i] = t % p; t /= p; }
        int ok = 1;
        for (int a = 1; a < q && ok; a++)
            for (int b = 1; b < q && ok; b++)
                if (polymul(a, b, p, k, pw, m) == 0) ok = 0;
        if (ok) {
            found = 1;
            for (int a = 0; a < q; a++)
                for (int b = 0; b < q; b++)
                    MULT[a][b] = polymul(a, b, p, k, pw, m);
        }
    }
    built_q = q;
}

/* ------------------------------------------------------------ group laws */

static int GFAM = 0, GORD = 0, GM = 1, GK = 1;
static int PWR[MAXN + 1];
static int GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Affine group F_q x| H, H the subgroup of order c in F_q^*. Element (a, h_j) = a*c + j. */
static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GORD = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    PWG[0] = 1;
    for (int i = 1; i < q - 1; i++) PWG[i] = MULT[PWG[i - 1]][g];
    int step = (q - 1) / c;
    for (int j = 0; j < q; j++) hidx[j] = -1;
    for (int t = 0; t < c; t++) {
        Hel[t] = PWG[(t * step) % (q - 1)];
        hidx[Hel[t]] = t;
    }
    for (int j = 0; j < c; j++)
        for (int t = 0; t < c; t++)
            HM[j * c + t] = hidx[MULT[Hel[j]][Hel[t]]];
}

/* Metacyclic group Z_m x| Z_k, element a*k + b, (a,b)(c,e) = (a + r^b c, b + e). */
static void set_group(const Grp *G) {
    GFAM = G->fam;
    if (GFAM == 0) {
        GM = G->m;
        GK = G->k;
        GORD = G->n;
        int r = G->r % GM;
        PWR[0] = 1 % GM;
        for (int b = 1; b < GK; b++) PWR[b] = (PWR[b - 1] * r) % GM;
    } else {
        setup_affine(G->q, G->p, G->kf, G->c);
    }
}

static inline int gmul(int x, int y) {
    if (GFAM == 0) {
        int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
        int na = (a + PWR[b] * c) % GM;
        return na * GK + (b + e) % GK;
    } else {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    }
}

static inline int ginv(int x) {
    if (GFAM == 0) {
        int a = x / GK, b = x % GK;
        int nb = (GK - b) % GK;
        int na = (GM - (PWR[nb] * a) % GM) % GM;
        return na * GK + nb;
    } else {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    }
}

/* Enumerate all groups of order n. Returns the count; if out != NULL and idx is in range,
 * fills *out with the idx-th group. Pass idx = -1 to count only. */
static int groups_for(int n, int idx, Grp *out) {
    int cnt = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, kf;
        if (n % q) continue;
        if (!factor_pp(q, &p, &kf)) continue;
        int c = n / q;
        if (c < 1 || (q - 1) % c) continue;
        if (cnt == idx && out) {
            memset(out, 0, sizeof *out);
            out->fam = 1; out->n = n; out->q = q; out->p = p; out->kf = kf; out->c = c;
        }
        cnt++;
    }
    for (int k = 1; k <= n; k++) {
        if (n % k) continue;
        int m = n / k;
        int rmax = (m == 1) ? 1 : m;
        for (int r = 0; r < rmax; r++) {
            if (m > 1 && gcd_i(r, m) != 1) continue;
            if (powmod(r, k, m) != 1 % m) continue;
            if (cnt == idx && out) {
                memset(out, 0, sizeof *out);
                out->fam = 0; out->n = n; out->m = m; out->k = k; out->r = r;
            }
            cnt++;
        }
    }
    return cnt;
}

/* ------------------------------------------------------------ lift state */

static int NN, SS, VV;                 /* group order, base size, total vertices */
static int P[MAXS][MAXD];              /* right endpoint of dart (i,t) */
static int cg[MAXS][MAXD];             /* voltage of dart (i,t) */
static int nbr[MAXV * MAXD];           /* adjacency slots */
static int vis[MAXV], que[MAXV];
static int stamp_ = 1;

/* Left (i,x) slot t -> right (P[i][t], x*g). Right (j,y) slot t -> left (i, y*g^-1). */
static void set_dart(int i, int t, int g) {
    int n = NN, s = SS;
    int j = P[i][t];
    int gi = ginv(g);
    for (int x = 0; x < n; x++) {
        int v = i * n + x;
        nbr[v * d + t] = s * n + j * n + gmul(x, g);
    }
    for (int y = 0; y < n; y++) {
        int w = s * n + j * n + y;
        nbr[w * d + t] = i * n + gmul(y, gi);
    }
    cg[i][t] = g;
}

static int conflict(int i, int t, int x) {
    for (int u = 0; u < d; u++)
        if (u != t && P[i][u] == P[i][t] && cg[i][u] == x) return 1;
    return 0;
}

static void make_pattern(int s) {
    for (int t = 0; t < d; t++) {
        int perm[MAXS];
        for (int i = 0; i < s; i++) perm[i] = i;
        for (int i = s - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i]; perm[i] = perm[j]; perm[j] = tmp;
        }
        for (int i = 0; i < s; i++) P[i][t] = perm[i];
    }
}

static int bfs_unreached(int src) {
    if (++stamp_ == 0x7fffffff) {
        memset(vis, 0, sizeof(vis));
        stamp_ = 1;
    }
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            const int *nb = nbr + v * d;
            for (int t = 0; t < d; t++) {
                int u = nb[t];
                if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
            }
        }
    }
    return VV - tail;
}

/* Sources: one identity vertex per base vertex (left and right). */
static long total_cost(void) {
    long c = 0;
    for (int u = 0; u < 2 * SS; u++) {
        int src = (u < SS) ? u * NN : SS * NN + (u - SS) * NN;
        c += bfs_unreached(src);
    }
    return c;
}

/* Simulated annealing on the voltages for the current group and pattern.
 * Returns 1 when every base vertex reaches everything within D. */
static int sa_run(int s, int n, double until) {
    SS = s;
    NN = n;
    VV = 2 * s * n;
    for (int i = 0; i < s; i++)
        for (int t = 0; t < d; t++) cg[i][t] = -1;
    for (int i = 0; i < s; i++)
        for (int t = 0; t < d; t++) {
            int x = 0, tries = 0;
            do { x = rndint(n); tries++; } while (conflict(i, t, x) && tries < 500);
            if (conflict(i, t, x)) return 0;
            set_dart(i, t, x);
        }
    long cost = total_cost();
    if (cost == 0) return 1;
    double c0 = (double)cost;
    double Ts = 0.05 * c0 + 1.0, Te = 0.3;
    for (int it = 0; it < ITERS && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) return 0;
        double T = Ts * pow(Te / Ts, (double)it / ITERS);
        int i = rndint(s), t = rndint(d), x = rndint(n);
        if (x == cg[i][t]) continue;
        if (conflict(i, t, x)) continue;
        int old = cg[i][t];
        set_dart(i, t, x);
        long c2 = total_cost();
        if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
            cost = c2;
        } else {
            set_dart(i, t, old);
        }
    }
    return cost == 0;
}

/* ------------------------------------------------------------ search driver */

static Grp bestG;
static int bestS = 0, bestN = 0, bestT = 0;
static int bestP[MAXS][MAXD], bestCg[MAXS][MAXD];

/* Try to find a valid lift with exactly T vertices. Returns 1 on success. */
static int try_T(int T, double until) {
    int vs[3], vn = 0;
    for (int s = 1; s <= 3; s++) {
        if (T % (2 * s)) continue;
        int n = T / (2 * s);
        if (n < d || n > MAXN) continue;
        if (groups_for(n, -1, NULL) > 0) vs[vn++] = s;
    }
    if (vn == 0) return 0;
    while (now() < until) {
        int s = vs[rndint(vn)];
        int n = T / (2 * s);
        int cnt = groups_for(n, -1, NULL);
        Grp G;
        groups_for(n, rndint(cnt), &G);
        set_group(&G);
        make_pattern(s);
        if (sa_run(s, n, until)) {
            if (T > bestT) {
                bestT = T;
                bestG = G;
                bestS = s;
                bestN = n;
                for (int i = 0; i < s; i++)
                    for (int t = 0; t < d; t++) {
                        bestP[i][t] = P[i][t];
                        bestCg[i][t] = cg[i][t];
                    }
            }
            return 1;
        }
    }
    return 0;
}

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
    t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXT) hi = MAXT;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    /* Phase 1: binary search over T in steps of 12 (divisible by 2, 4 and 6). */
    long a = (lo + 11) / 12, b = hi / 12;
    while (a <= b && now() < t_end) {
        long mid = (a + b) / 2;
        long span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_T((int)(mid * 12), now() + slice)) a = mid + 1;
        else b = mid - 1;
    }

    /* Phase 2: sweep upward from the best order in steps of 2. */
    int T = bestT > 0 ? bestT + 2 : lo;
    int fails = 0;
    while (now() < t_end && fails < 3 && T <= hi) {
        if (T <= bestT) { T = bestT + 2; continue; }
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (try_T(T, now() + slice)) fails = 0;
        else fails++;
        T += 2;
    }

    if (bestT <= 0) { printf("0 0\n"); return 0; }
    set_group(&bestG);
    NN = bestN;
    SS = bestS;
    VV = 2 * SS * NN;
    for (int i = 0; i < SS; i++)
        for (int t = 0; t < d; t++) P[i][t] = bestP[i][t];
    printf("%d %d\n", VV, SS * NN * d);
    for (int i = 0; i < SS; i++)
        for (int x = 0; x < NN; x++)
            for (int t = 0; t < d; t++) {
                int j = P[i][t];
                int y = gmul(x, bestCg[i][t]);
                printf("%d %d\n", i * NN + x, SS * NN + j * NN + y);
            }
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

    # Voltage lifts over affine and metacyclic groups with 1x1, 2x2 and 3x3 base graphs.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 2.0
        lo = best[0] + 1
        hi = min(mb, 6000)
        if budget > 3.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass  # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
