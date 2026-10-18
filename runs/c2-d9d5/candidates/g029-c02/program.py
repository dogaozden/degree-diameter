"""Single-orbit lifts over semidirect groups Z_m x|_r Z_k for the bipartite degree-diameter problem.

New idea in this version: the parent searches only affine groups F_q x| H, which
exist only for orders q*c with c | q-1. Here the engine also searches semidirect
products Z_m x|_r Z_k (element (a,b), product (a,b)(c,e) = (a + r^b c, b+e),
requiring r^k = 1 mod m and gcd(r,m) = 1). These exist for every order N = m*k,
so the engine can scan every N just above the current best instead of jumping
between prime-power-based orders. Each candidate (m, k, r) gives a 2N-vertex
d-regular bipartite lift: L_g ~ R_(g*v_t) for d darts with distinct voltages v_t.
Left translations are automorphisms, so BFS from L_e and R_e decides the diameter.

Search: an affine binary search runs first (short share of time). Then the semidirect
phase scans orders N in ascending windows, tries each candidate with simulated
annealing over voltages, and records every success. Before output the C engine
re-checks the graph with a full BFS from every vertex when small enough. Python
verifies the result with lib.is_valid and keeps a valid fallback.
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
#define MAXCAND 20000

typedef struct { int typ, N, q, p, kf, c, m, kz, r; } Cand;

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
/* typ 0: affine group F_q x| H, elements a*GC + j.
 * typ 1: semidirect Z_SM x|_SR Z_SK, elements a*SK + b, (a,b)(c,e) = (a + r^b c, b+e). */

static int gtyp = -1;
static int GN;
static int GQ, GC;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int SM, SK, SR;
static int SPW[MAXN];

static void setup_affine(int q, int p, int k, int c) {
    build_field(q, p, k);
    gtyp = 0;
    GQ = q;
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
    gtyp = 1;
    SM = m;
    SK = k;
    SR = r;
    GN = m * k;
    SPW[0] = 1 % m;
    for (int i = 1; i < k; i++) SPW[i] = (int)((long)SPW[i - 1] * r % m);
}

static inline int gmul(int x, int y) {
    if (gtyp == 1) {
        int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
        int na = (int)(((long)a + (long)SPW[b] * c) % SM);
        int nb = b + e;
        if (nb >= SK) nb -= SK;
        return na * SK + nb;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    if (gtyp == 1) {
        int a = x / SK, b = x % SK;
        int nb = (SK - b) % SK;
        int na = (int)((SM - ((long)SPW[nb] * a) % SM) % SM);
        return na * SK + nb;
    }
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ single-orbit lift */
/* Left vertex g is index g, right vertex y is index N + y.
 * Dart t with voltage v: L_g ~ R_(g*v). */

static int vol[MAXD];
static int fw[MAXD][MAXN], bw[MAXD][MAXN];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;

static int bestN = 0;
static Cand bestC;
static int bestVol[MAXD];

static void set_dart(int t, int x) {
    vol[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[t][g] = gmul(g, x);
        bw[t][g] = gmul(g, xi);
    }
}

static int valid_value(int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && vol[t2] == x) return 0;
    return 1;
}

static inline int nbr(int v, int t) {
    int N = GN;
    return v < N ? N + fw[t][v] : bw[t][v - N];
}

/* BFS up to depth D from src; returns number of vertices reached. */
static int bfs_count(int src) {
    int N = GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < N) {
                for (int t = 0; t < d; t++) {
                    int u = N + fw[t][v];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int x = v - N;
                for (int t = 0; t < d; t++) {
                    int u = bw[t][x];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached vertices from L_e and R_e (the two orbit representatives). */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

/* Simulated annealing over voltages with random restarts.
 * Returns 1 with a cost-0 state in vol, 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        for (int t = 0; t < d; t++) {
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(t, x, t) && tries < 100000);
            set_dart(t, x);
        }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int t = rndint(d);
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[t];
            set_dart(t, x);
            long c2 = cover_cost();
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

/* ------------------------------------------------------------ candidates */

static Cand acand[MAXCAND];
static int nac = 0;
static Cand scand[MAXCAND];
static int nsc = 0;
static int sols[MAXN];
static Cand tmpb[512];

static long modpow(long b, long e, long m) {
    long r = 1 % m, x = b % m;
    while (e > 0) {
        if (e & 1) r = r * x % m;
        x = x * x % m;
        e >>= 1;
    }
    return r;
}

static int gcdi(int a, int b) {
    while (b) { int t = a % b; a = b; b = t; }
    return a;
}

static void build_affine_cands(int lo, int hi) {
    nac = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nac < MAXCAND) {
                Cand cd;
                memset(&cd, 0, sizeof cd);
                cd.typ = 0; cd.N = (int)N; cd.q = q; cd.p = p; cd.kf = k; cd.c = c;
                acand[nac++] = cd;
            }
        }
    }
    for (int i = 1; i < nac; i++) {
        Cand t = acand[i];
        int j = i - 1;
        while (j >= 0 && acand[j].N > t.N) { acand[j + 1] = acand[j]; j--; }
        acand[j + 1] = t;
    }
}

/* All semidirect candidates with N in [lo, hi]: for each divisor k >= 2 of N
 * (m = N/k >= 3), up to two random r with r^k = 1 mod m and gcd(r, m) = 1.
 * Candidates of one N are shuffled. */
static void build_semi_cands(int lo, int hi) {
    nsc = 0;
    for (int N = lo; N <= hi; N++) {
        int nb = 0;
        for (int k = 2; 3 * k <= N; k++) {
            if (N % k) continue;
            int m = N / k;
            int ns = 0;
            for (int r = 1; r < m; r++) {
                if (gcdi(r, m) != 1) continue;
                if (modpow(r, k, m) != 1) continue;
                sols[ns++] = r;
            }
            if (ns == 0) continue;
            int first = rndint(ns);
            int picks[2] = {first, -1};
            if (ns >= 2) {
                int s2 = rndint(ns - 1);
                if (s2 >= first) s2++;
                picks[1] = s2;
            }
            for (int s = 0; s < 2 && picks[s] >= 0; s++) {
                if (nb < 510) {
                    Cand cd;
                    memset(&cd, 0, sizeof cd);
                    cd.typ = 1; cd.N = N; cd.m = m; cd.kz = k; cd.r = sols[picks[s]];
                    tmpb[nb++] = cd;
                }
            }
        }
        for (int i = nb - 1; i > 0; i--) {
            int j = rndint(i + 1);
            Cand t = tmpb[i];
            tmpb[i] = tmpb[j];
            tmpb[j] = t;
        }
        for (int i = 0; i < nb && nsc < MAXCAND; i++) scand[nsc++] = tmpb[i];
    }
}

static void record(Cand cd) {
    if (cd.N <= bestN) return;
    bestN = cd.N;
    bestC = cd;
    for (int t = 0; t < d; t++) bestVol[t] = vol[t];
}

/* Binary search over affine orders; the semidirect phase handles larger orders. */
static void affine_phase(int lo, int hi, double until) {
    build_affine_cands(lo, hi);
    int a = 0, b = nac - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        double rem = until - now();
        double slice = rem * 0.25;
        if (slice < 1.5) slice = 1.5;
        if (slice > rem) slice = rem;
        Cand cd = acand[mid];
        setup_affine(cd.q, cd.p, cd.kf, cd.c);
        if (search_group(now() + slice)) {
            record(cd);
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }
}

/* Ascending scan over semidirect candidates, windows of 60 orders.
 * Each success raises the bar, so the scan keeps climbing while time remains. */
static void semi_phase(int lo, int hi, double until) {
    int start = lo;
    while (now() < until) {
        if (start < bestN + 1) start = bestN + 1;
        if (start > hi) break;
        int wend = start + 59;
        if (wend > hi) wend = hi;
        build_semi_cands(start, wend);
        for (int i = 0; i < nsc && now() < until; i++) {
            Cand cd = scand[i];
            if (cd.N <= bestN) continue;
            double rem = until - now();
            double slice = rem * 0.06;
            if (slice < 0.8) slice = 0.8;
            if (slice > 4.0) slice = 4.0;
            if (slice > rem) slice = rem;
            setup_semi(cd.m, cd.kz, cd.r);
            if (search_group(now() + slice)) record(cd);
        }
        start = wend + 1;
    }
}

/* ------------------------------------------------------------ main */

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    int lo1 = atoi(argv[5]), hi1 = atoi(argv[6]);
    int lo3 = atoi(argv[7]), hi3 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) {
        printf("0 0\n");
        return 0;
    }
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (hi3 > MAXN - 1) hi3 = MAXN - 1;
    if (lo1 < 2 * d) lo1 = 2 * d;
    if (lo3 < 2 * d) lo3 = 2 * d;

    double span = t_end - t0;
    if (lo1 <= hi1) affine_phase(lo1, hi1, t0 + 0.3 * span);
    if (lo3 <= hi3) semi_phase(lo3, hi3, t_end);

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }

    /* Rebuild the best graph. */
    if (bestC.typ == 0) setup_affine(bestC.q, bestC.p, bestC.kf, bestC.c);
    else setup_semi(bestC.m, bestC.kz, bestC.r);
    for (int t = 0; t < d; t++) set_dart(t, bestVol[t]);

    int N = GN, V = 2 * N, E = N * d;

    /* Full check from every vertex when cheap; symmetry is the fallback. */
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
                    for (int t = 0; t < d; t++) {
                        int u = nbr(v, t);
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
    for (int v = 0; v < N; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, N + fw[t][v]);
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

    # Single-orbit lifts over affine and semidirect groups. Order N gives 2N vertices.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        hi = min(mb // 2, 4799)
        lo = max(2 * d, best[0] // 2 + 1, mb // 10)
        if budget > 2.0 and lo <= hi:
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo, hi, lo, hi],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
