"""Mixed-orbit affine and metacyclic lifts for the bipartite degree-diameter problem.

Changes from the two-orbit parent:
  * The base graph has B = 1..4 orbits per side. Each dart-slot t uses a random
    permutation of the B orbits, so every left and right orbit gets exactly d darts.
  * Two group families are searched: the affine group F_q x| H and the metacyclic
    group Z_m x| Z_k with r^k = 1 mod m.
  * B = 1 is searched first, then B = 3, 2 and 4. Each later phase only looks for
    orders that beat the current best total, 2*B*N > best.

Validity: left translations are automorphisms that act transitively on every
orbit, so a BFS from one representative per orbit decides the diameter. Voltages
on darts with the same (left orbit, right orbit) pair are kept distinct, so the
graph is simple and d-regular. The C engine re-checks small graphs with a full BFS
before printing. Python checks the result with lib.is_valid and keeps a valid
fallback.
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

#define MAXQ 256
#define MAXC 256
#define MAXN 4800
#define MAXD 32
#define MAXB 4
#define MAXV (2 * MAXB * MAXN)
#define MAXCAND 60000

typedef struct { int type, q, p, kf, c, r, N; } Cand;

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
static int gcd_i(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}
static long powmod_l(long b, long e, long m) {
    long r = 1 % m;
    b %= m;
    while (e > 0) {
        if (e & 1) r = r * b % m;
        b = b * b % m;
        e >>= 1;
    }
    return r;
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

/* ------------------------------------------------------------ groups */

static int gtype = 0, GN = 0;
static int GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int SM, SK;
static int SPOW[MAXC];

/* Affine group F_q x| H, element a*GC + j with H = {Hel[j]} of order c. */
static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtype = 0;
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0 < q && g < 0; g0++) {
        int x = 1, ord = 0;
        do { x = MULT[x][g0]; ord++; } while (x != 1 && ord < q);
        if (ord == q - 1) g = g0;
    }
    if (g < 0) g = 2;
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
static void setup_semi(int m, int k, int r) {
    gtype = 1;
    SM = m;
    SK = k;
    GN = m * k;
    SPOW[0] = 1 % m;
    for (int b = 1; b < k; b++) SPOW[b] = (int)((long)SPOW[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
        int na = ADDT[a][MULT[Hel[j]][b]];
        return na * GC + HM[j * GC + t];
    } else {
        int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
        int na = (int)(((long)a + (long)SPOW[b] * c) % SM);
        return na * SK + (b + e) % SK;
    }
}

static int ginv(int x) {
    if (gtype == 0) {
        int a = x / GC, j = x % GC;
        int jn = (GC - j) % GC;
        int na = NEGT[MULT[Hel[jn]][a]];
        return na * GC + jn;
    } else {
        int a = x / SK, b = x % SK;
        int nb = (SK - b) % SK;
        int na = (int)(((long)(SM - SPOW[nb]) * a) % SM);
        return na * SK + nb;
    }
}

static void setup_cand(const Cand *cd) {
    if (cd->type == 0) setup_affine(cd->q, cd->p, cd->kf, cd->c);
    else setup_semi(cd->q, cd->c, cd->r);
}

/* ------------------------------------------------------------ lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static int bestTotal = 0, bestB = 0;
static Cand bestCd;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];

static void build_incidence(int B) {
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

/* Each dart slot t is a permutation of the B orbits, so every orbit has d darts
 * on each side. */
static void random_pattern(int B) {
    curB = B;
    for (int t = 0; t < d; t++) {
        int perm[MAXB];
        for (int i = 0; i < B; i++) perm[i] = i;
        for (int i = B - 1; i > 0; i--) {
            int j = rndint(i + 1);
            int tmp = perm[i];
            perm[i] = perm[j];
            perm[j] = tmp;
        }
        for (int i = 0; i < B; i++) tgt[i][t] = perm[i];
    }
    build_incidence(B);
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    int N = GN;
    for (int g = 0; g < N; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* Darts of the same (orbit, target) class need distinct voltages (simple graph). */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

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

/* Unreached pairs from the 2B orbit representatives. */
static long cover_cost(void) {
    int N = GN, B = curB, V = 2 * B * N;
    long cost = 0;
    for (int i = 0; i < B; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < B; j++) cost += (long)(V - bfs_count(B * N + j * N));
    return cost;
}

/* Simulated annealing over the voltages, restarting with new base patterns.
 * Returns 1 with a cost-0 state left in tgt/vol, 0 on timeout. */
static int search_group(int B, double until) {
    int N = GN;
    const int iters = 6000;
    while (now() < until) {
        random_pattern(B);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x = 0, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x = 0, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(i, t, x, d) && tries < 1000);
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
        if (cost == 0) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand cand[MAXCAND];
static int nc = 0;

static void add_cand(Cand cd) {
    if (nc < MAXCAND) cand[nc++] = cd;
}

static int cmp_cand(const void *a, const void *b) {
    const Cand *x = (const Cand *)a, *y = (const Cand *)b;
    return (x->N > y->N) - (x->N < y->N);
}

static void build_cands(int lo, int hi) {
    nc = 0;
    if (lo < 1) lo = 1;
    if (hi > MAXN - 1) hi = MAXN - 1;
    /* Affine groups F_q x| H with c >= 2. */
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            Cand cd = {0, q, p, k, c, 0, (int)N};
            add_cand(cd);
        }
    }
    /* Metacyclic groups Z_m x| Z_k with a small r of order dividing k. */
    for (int m = 3; m <= MAXN; m++) {
        for (int k = 2; k < MAXC && (long)m * k <= hi; k++) {
            long N = (long)m * k;
            if (N < lo) continue;
            int rr = 0;
            for (int r = 2; r < m && r <= 64; r++) {
                if (gcd_i(r, m) != 1) continue;
                if (powmod_l(r, k, m) == 1 % m) { rr = r; break; }
            }
            if (rr) {
                Cand cd = {1, m, 0, 0, k, rr, (int)N};
                add_cand(cd);
            }
        }
    }
    if (nc > 1) qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);
}

static void record(int B, const Cand *cd) {
    int total = 2 * B * cd->N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestCd = *cd;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
}

/* Binary search over candidate orders for a feasible one, then extend upward. */
static void search_phase(int B, int lo, int hi, double until) {
    build_cands(lo, hi);
    if (nc == 0) return;
    double span = until - now();
    int a = 0, b = nc - 1, bestIdx = -1, bestNp = 0;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = span / 8.0;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(&cand[mid]);
        if (search_group(B, now() + slice)) {
            record(B, &cand[mid]);
            if (cand[mid].N > bestNp) { bestNp = cand[mid].N; bestIdx = mid; }
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
    if (bestIdx < 0) return;
    int fails = 0;
    for (int idx = bestIdx + 1; idx < nc && fails < 3 && now() < until; idx++) {
        if (cand[idx].N <= bestNp) continue;
        double rem = until - now();
        double slice = rem * 0.4;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_cand(&cand[idx]);
        if (search_group(B, now() + slice)) {
            record(B, &cand[idx]);
            bestNp = cand[idx].N;
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 13) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo[MAXB + 1], hi[MAXB + 1];
    for (int B = 1; B <= MAXB; B++) {
        lo[B] = atoi(argv[3 + 2 * B]);
        hi[B] = atoi(argv[4 + 2 * B]);
    }
    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    double t0 = now();
    double T = limit * 0.9 - 0.5;
    if (T < 1.0) {
        printf("0 0\n");
        return 0;
    }
    t_end = t0 + T;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    static const double share[MAXB + 1] = {0.0, 0.35, 0.20, 0.25, 0.20};
    double cum = 0.0;
    for (int B = 1; B <= MAXB; B++) {
        cum += share[B];
        double until = (B == MAXB) ? t_end : t0 + T * cum;
        int l = lo[B], h = hi[B];
        if (l < d + 1) l = d + 1;
        if (h > MAXN - 1) h = MAXN - 1;
        if (bestTotal > 0) {
            int nl = bestTotal / (2 * B) + 1;   /* need 2*B*N > bestTotal */
            if (nl > l) l = nl;
        }
        if (l <= h && now() < until) search_phase(B, l, h, until);
    }

    if (bestTotal == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    int B = bestB;
    setup_cand(&bestCd);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    build_incidence(B);
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
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

    /* Full BFS from every vertex when cheap, as a safety net. */
    if (V <= 6000) {
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

    # Mixed-orbit lifts. Order N with B orbits per side gives 2*B*N vertices.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        if budget > 4.0:
            args = [d, D, seed, round(budget, 2)]
            for B in range(1, 5):
                hi = min(4799, mb // (2 * B))
                args += [d + 1, hi]
            try:
                text = lib.run_c(C_SOURCE, args, stdin_graph=None,
                                 timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
