"""Multi-orbit bi-Cayley lifts for the bipartite degree-diameter problem.

Change in this version: the search no longer uses one fixed group family and one
fixed base pattern. Each side is split into B orbits (B = 1, 2, 3). The group is
chosen per restart from three families: the affine groups F_q x| H, the
semidirect products Z_m x|_r Z_k (including cyclic Z_N), with a random valid r.
The base multigraph is a random union of d permutations of the B orbits, so every
orbit has degree d on both sides. Voltages are annealed so that BFS from the 2B
orbit representatives reaches every vertex within D steps. This gives all integers
N as candidate orbit sizes, not only q*c. Feasibility is monotone enough for a
binary search over N, and the best total 2BN is kept. Before output the C engine
re-checks the full graph when it is small. Python validates the result with
lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit bi-Cayley lifts over semidirect groups.
 * Left vertex (i,g) ~ right vertex (j, g*v) for each dart (i,t) with
 * target j = tgt[i][t] and voltage v = vol[i][t].
 * Group families: 0 = affine F_q x| H, 1 = Z_m x|_r Z_k (k = 1 gives cyclic).
 * Left translations are automorphisms, transitive on each orbit, so BFS from the
 * 2B representatives decides the diameter.
 * Usage: prog d D seed time_limit lo1 hi1 lo2 hi2 lo3 hi3
 * Output: "n m" then m lines "u v", or "0 0".
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
#define MAXN 4800
#define MAXD 32
#define MAXB 3
#define MAXV (2*MAXB*MAXN)
#define MAXOPT 64

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

/* ------------------------------------------------------------ groups */

static int gtype = 0;          /* 0 affine, 1 semidirect Z_m x| Z_k */
static int gA = 0, gB = 0, gR = 1;
static int GN = 0;
static int GC = 1;             /* affine: |H| */
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int SM = 1, SK = 1;     /* semidirect: m and k */
static int RP[MAXC];           /* RP[b] = r^b mod m */

static void setup_affine(int q, int c) {
    int p, k;
    factor_pp(q, &p, &k);
    build_field(q, p, k);
    gtype = 0; gA = q; gB = c; gR = 1;
    GC = c;
    GN = q * c;
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

static void setup_semi(int m, int k, int r) {
    gtype = 1; gA = m; gB = k; gR = r;
    SM = m; SK = k; GN = m * k;
    RP[0] = 1 % m;
    for (int b = 1; b < k; b++) RP[b] = (int)(((long)RP[b - 1] * r) % m);
}

static void setup_group(int type, int A, int B, int R) {
    if (type == 0) setup_affine(A, B);
    else setup_semi(A, B, R);
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    } else {
        int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
        int na = (int)((a + (long)RP[b] * c) % SM);
        return na * SK + (b + e) % SK;
    }
}

static inline int ginv(int x) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    } else {
        int a = x / SK, b = x % SK;
        int nb = (SK - b) % SK;
        int na = (int)((SM - ((long)RP[nb] * a) % SM) % SM);
        return na * SK + nb;
    }
}

typedef struct { int type, A, B; } Opt;

static int gcd_int(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static int powmod(int b, int e, int m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return (int)r;
}

/* All group options of order N: cyclic and semidirect (m, k) with k <= 255, and affine. */
static int make_opts(int N, Opt *o, int maxo) {
    int n = 0;
    for (int k = 1; k < MAXC && 2 * k <= N; k++) {
        if (N % k) continue;
        if (n < maxo) { o[n].type = 1; o[n].A = N / k; o[n].B = k; n++; }
    }
    for (int q = 3; q < MAXQ && q <= N; q++) {
        if (N % q) continue;
        int c = N / q;
        if (c < 2 || c > q - 1 || (q - 1) % c) continue;
        int p, kk;
        if (!factor_pp(q, &p, &kk)) continue;
        if (n < maxo) { o[n].type = 0; o[n].A = q; o[n].B = c; n++; }
    }
    return n;
}

/* Random r with gcd(r,m)=1 and r^k = 1 mod m; falls back to r = 1 (always valid). */
static int pick_r(int m, int k) {
    if (k == 1 || m < 3) return 1;
    for (int tr = 0; tr < 64; tr++) {
        int r = 1 + rndint(m - 1);
        if (gcd_int(r, m) == 1 && powmod(r, k, m) == 1 % m) return r;
    }
    return 1;
}

/* ------------------------------------------------------------ lift state */

static int curB = 1;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestTotal = 0, bestB = 0, bestN = 0;
static int bestType = 0, bestA = 0, bestBp = 0, bestR = 1;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

/* Incoming darts of each right orbit j: exactly d of them. */
static void build_inc(int B) {
    curB = B;
    for (int j = 0; j < B; j++) {
        int cnt = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++)
                if (tgt[i][t] == j && cnt < MAXD) {
                    incI[j][cnt] = i;
                    incT[j][cnt] = t;
                    cnt++;
                }
    }
}

/* Base multigraph: d random permutations of the B orbits (B = 1 is a single dart class). */
static void random_base(int B) {
    curB = B;
    if (B == 1) {
        for (int t = 0; t < d; t++) tgt[0][t] = 0;
    } else {
        for (int t = 0; t < d; t++) {
            int perm[MAXB];
            for (int i = 0; i < B; i++) perm[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int j = rndint(i + 1);
                int x = perm[i]; perm[i] = perm[j]; perm[j] = x;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = perm[i];
        }
    }
    build_inc(B);
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Darts of the same (i, target) class need distinct voltages so the graph is simple. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static void init_darts(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int x, tries = 0;
            do { x = rndint(GN); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
            set_dart(i, t, x);
        }
}

/* BFS up to depth D; returns the number of vertices reached. */
static int bfs_count(int src) {
    int N = GN, BN = curB * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < BN) {
                int i = v / N, g = v % N;
                for (int t = 0; t < d; t++) {
                    int u = BN + tgt[i][t] * N + fw[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, x = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bw[i][t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from the 2B orbit representatives. */
static long cover_cost(void) {
    int N = GN, BN = curB * N, V = 2 * BN;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count(BN + j * N));
    return cost;
}

static void record(int B, int N) {
    int total = 2 * B * N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestN = N;
    bestType = gtype;
    bestA = gA;
    bestBp = gB;
    bestR = gR;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Restarts with random group, base and voltages for a fixed N until time 'until'. */
static int search_N(int B, int N, double until) {
    Opt opts[MAXOPT];
    while (now() < until) {
        int no = make_opts(N, opts, MAXOPT);
        if (no == 0) return 0;
        Opt o = opts[rndint(no)];
        if (o.type == 0) setup_affine(o.A, o.B);
        else setup_semi(o.A, o.B, pick_r(o.A, o.B));
        random_base(B);
        init_darts(B);
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        const int iters = 8000;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
            do { x = rndint(GN); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[i][t];
            set_dart(i, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_dart(i, t, old);
            }
        }
        if (cost == 0) {
            record(B, N);
            return 1;
        }
    }
    return 0;
}

/* Binary search over N in [lo, hi] (feasibility is treated as monotone), then extend upward. */
static void search_phase(int B, int lo, int hi, double until) {
    if (lo < 2 * d) lo = 2 * d;
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo > hi) return;
    int a = lo, b = hi, bestNp = 0;
    while (a <= b && now() < until) {
        int mid = a + (b - a) / 2;
        double rem = until - now();
        double slice = rem * 0.12;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        if (search_N(B, mid, now() + slice)) {
            if (mid > bestNp) bestNp = mid;
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bestNp == 0) return;
    int N = bestNp + 1, fails = 0;
    while (N <= hi && fails < 2 && now() < until) {
        double rem = until - now();
        double slice = rem * 0.5;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        if (search_N(B, N, now() + slice)) {
            bestNp = N;
            fails = 0;
        } else {
            fails++;
        }
        N++;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 11) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo[4], hi[4];
    for (int B = 1; B <= 3; B++) {
        lo[B] = atoi(argv[3 + 2 * B]);
        hi[B] = atoi(argv[4 + 2 * B]);
    }
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    for (int B = 1; B <= 3; B++) {
        if (hi[B] > MAXN - 1) hi[B] = MAXN - 1;
        if (lo[B] < 2 * d) lo[B] = 2 * d;
    }

    double span = t_end - t0;
    if (span > 1.0) {
        search_phase(1, lo[1], hi[1], t0 + span * 0.30);
        int l2 = lo[2];
        if (bestTotal / 4 + 1 > l2) l2 = bestTotal / 4 + 1;
        search_phase(2, l2, hi[2], t0 + span * 0.60);
        int l3 = lo[3];
        if (bestTotal / 6 + 1 > l3) l3 = bestTotal / 6 + 1;
        search_phase(3, l3, hi[3], t0 + span * 0.80);
        if (bestTotal > 0) {
            int B = bestB;
            int nlo = bestTotal / (2 * B) + 1;
            if (nlo < lo[B]) nlo = lo[B];
            search_phase(B, nlo, hi[B], t_end);
        }
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    setup_group(bestType, bestA, bestBp, bestR);
    curB = bestB;
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    build_inc(bestB);
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = bestB * N, V = 2 * BN, E = BN * d;
    static int adj[MAXV][MAXD];
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adj[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adj[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Full check from every vertex when cheap. */
    if (V <= 5000) {
        for (int s = 0; s < V; s++) {
            stamp_++;
            int head = 0, tail = 0;
            que[tail++] = s;
            vis[s] = stamp_;
            for (int lvl = 0; lvl < D && head < tail; lvl++) {
                int end = tail;
                while (head < end) {
                    int v = que[head++];
                    for (int k = 0; k < d; k++) {
                        int u = adj[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) {
                printf("0 0\n");
                return 0;
            }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adj[v][t]);
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

    # Multi-orbit lifts. A total of 2BN vertices needs N in [lo_B, hi_B].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 2.0:
            ranges = []
            for B in (1, 2, 3):
                lo = max(2 * d, best[0] // (2 * B) + 1, mb // (8 * B))
                hi = min(mb // (2 * B), 4799)
                ranges += [lo, hi]
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), *ranges],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
