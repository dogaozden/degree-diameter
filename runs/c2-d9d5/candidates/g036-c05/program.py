"""Bandit-scheduled search over mixed groups for the bipartite degree-diameter problem.

New idea in this version: the parent spends most of its budget on two-orbit lifts (B = 2),
which never produced a feasible graph, and then binary-searches a single family of
affine groups F_q x| H. Here:

  * B = 2 is dropped. All time goes to one-orbit (Haar) lifts Cay-type bipartite graphs
    L_g ~ R_{g v} for v in S, |S| = d, over a MIXED family of groups:
      - affine groups F_q x| H (order q*c, as in the parent), and
      - metacyclic groups Z_m x|_r Z_k (r^k = 1 mod m), which are non-abelian for r != 1
        and give many more group orders.
  * Left translations are automorphisms transitive on each side, so the diameter is
    decided by two BFS runs (from L_e and R_e).
  * Scheduling is a successive-allocation bandit on normalized cover cost (uncovered
    pairs divided by 2N). Phase 1 gives every sampled candidate a short anneal and
    records the best normalized cost it reaches. Phase 2 repeatedly gives a longer
    slice to the candidate with the lowest recorded cost among those with order above
    the best solved so far. Feasibility is therefore pursued where the search is
    closest to success, instead of by a fixed binary search.
  * The C engine re-checks the final graph with a full BFS from every vertex when it has
    at most 5000 vertices, and prints "0 0" on failure. Python checks everything with
    lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* One-orbit Haar lifts over mixed groups, scheduled by a cost bandit.
 * Group G of order N. Left vertex g ~ right vertex y = g*v_t for darts t = 0..d-1.
 * Families: 0 = affine F_q x| H (q prime power < 256, c | q-1, c >= 2);
 *           1 = metacyclic Z_m x|_r Z_k (r^k = 1 mod m).
 * Usage: prog d D seed time_limit lo hi
 * Output: "n m" then m lines "u v" (left vertices 0..N-1, right N..2N-1), or "0 0".
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
#define MAXAFF 4096
#define MAXSEM 30000
#define ITERS 8000
#define SEM_MMAX 700

typedef struct {
    int fam;            /* 0 affine, 1 metacyclic */
    int q, p, pk, c;    /* affine parameters */
    int m, k, r;        /* metacyclic parameters */
    int N;
    double best;        /* lowest normalized cover cost seen so far */
    double slice;       /* last time slice given */
    int tried;
} Cand;

static int d, D;
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

static int GFAM = 0;
static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];
static int SM, SK, SR, SPW[MAXN];

static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GFAM = 0;
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

/* (a,b)*(c,e) = (a + r^b c, b + e) on Z_m x Z_k, coded a*k+b. Identity is 0. */
static void setup_semi(int m, int k, int r) {
    GFAM = 1;
    SM = m;
    SK = k;
    SR = r % m;
    GN = m * k;
    SPW[0] = 1 % m;
    for (int b = 1; b < k; b++) SPW[b] = (int)(((long)SPW[b - 1] * SR) % m);
}

static inline int gmul(int x, int y) {
    if (GFAM == 1) {
        int a = x / SK, b = x % SK, c = y / SK, e = y % SK;
        int na = (int)(((long)a + (long)SPW[b] * c) % SM);
        int nb = (b + e) % SK;
        return na * SK + nb;
    }
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    if (GFAM == 1) {
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

static void setup_cand(const Cand *cd) {
    if (cd->fam == 0) setup_group(cd->q, cd->p, cd->pk, cd->c);
    else setup_semi(cd->m, cd->k, cd->r);
}

/* ------------------------------------------------------------ lift state */

static int fw[MAXD][MAXN], bw[MAXD][MAXN], vol[MAXD];
static int vis[2 * MAXN], que[2 * MAXN];
static int stamp_ = 0;
static double runBest;
static int bestN = 0;
static Cand bestCand;
static int bestVol[MAXD];

/* Voltage of dart t is x: L_g ~ R_{g x}; R_y ~ L_{y x^-1}. */
static void set_dart(int t, int x) {
    vol[t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[t][g] = gmul(g, x);
        bw[t][g] = gmul(g, xi);
    }
}

/* Darts need distinct voltages so the graph is simple. */
static int valid_value(int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && vol[t2] == x) return 0;
    return 1;
}

/* BFS up to depth D from v; returns number of vertices reached. */
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
                int y = v - N;
                for (int t = 0; t < d; t++) {
                    int u = bw[t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from the two orbit representatives L_e and R_e. */
static long cover_cost(void) {
    int V = 2 * GN;
    return (long)(V - bfs_count(0)) + (long)(V - bfs_count(GN));
}

/* Simulated annealing over the voltages of the current group.
 * Returns 1 with a cost-0 state (vol holds it), 0 on timeout.
 * runBest is set to the lowest normalized cost (cost / 2N) seen. */
static int search_group(double until) {
    int N = GN;
    double V = 2.0 * N;
    runBest = 1e18;
    while (now() < until) {
        for (int t = 0; t < d; t++) {
            int x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(t, x, t) && tries < 100000);
            set_dart(t, x);
        }
        long cost = cover_cost();
        if (cost / V < runBest) runBest = cost / V;
        if (cost == 0) return 1;
        double Ts = 0.05 * (double)cost + 1.0, Te = 0.3;
        for (int it = 0; it < ITERS; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / ITERS);
            int t = rndint(d), x, tries = 0;
            do { x = rndint(N); tries++; } while (!valid_value(t, x, d) && tries < 1000);
            if (tries >= 1000) continue;
            int old = vol[t];
            set_dart(t, x);
            long c2 = cover_cost();
            if (c2 / V < runBest) runBest = c2 / V;
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
                if (cost == 0) return 1;
            } else {
                set_dart(t, old);
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates */

static Cand aff[MAXAFF];
static int naff = 0;
static Cand sem[MAXSEM];
static int nsem = 0;
static long seen_sem = 0;
static Cand cand[MAXAFF + MAXSEM];
static int nc = 0;

/* Reservoir sampling keeps a uniform subset of the metacyclic candidates. */
static void sem_offer(Cand cd) {
    seen_sem++;
    if (nsem < MAXSEM) {
        sem[nsem++] = cd;
    } else {
        long j = (long)(rnd() % (uint64_t)seen_sem);
        if (j < MAXSEM) sem[j] = cd;
    }
}

static void build_cands(int lo, int hi) {
    naff = 0;
    nsem = 0;
    seen_sem = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, kk;
        if (!factor_pp(q, &p, &kk)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (naff < MAXAFF) {
                Cand cd;
                memset(&cd, 0, sizeof cd);
                cd.fam = 0; cd.q = q; cd.p = p; cd.pk = kk; cd.c = c;
                cd.N = (int)N; cd.best = 1e18;
                aff[naff++] = cd;
            }
        }
    }
    int mmax = hi / 2;
    if (mmax > SEM_MMAX) mmax = SEM_MMAX;
    for (int mm = 3; mm <= mmax; mm++) {
        int kstart = (lo + mm - 1) / mm;
        if (kstart < 2) kstart = 2;
        for (int kk = kstart; (long)mm * kk <= hi; kk++) {
            for (int r = 1; r < mm; r++) {
                if (powmod(r, kk, mm) != 1 % mm) continue;
                Cand cd;
                memset(&cd, 0, sizeof cd);
                cd.fam = 1; cd.m = mm; cd.k = kk; cd.r = r;
                cd.N = mm * kk; cd.best = 1e18;
                sem_offer(cd);
            }
        }
    }
    nc = 0;
    for (int i = 0; i < naff; i++) cand[nc++] = aff[i];
    for (int i = 0; i < nsem; i++) cand[nc++] = sem[i];
}

static void on_solve(const Cand *cd) {
    if (cd->N <= bestN) return;
    bestN = cd->N;
    bestCand = *cd;
    for (int t = 0; t < d; t++) bestVol[t] = vol[t];
}

/* Phase 1: short anneal for each candidate in random order (up to 40% of the time).
 * Phase 2: repeatedly give a growing slice to the candidate with the lowest cost
 * among those whose order is above the best solved so far. */
static void schedule(double until) {
    for (int i = nc - 1; i > 0; i--) {
        int j = rndint(i + 1);
        Cand tmp = cand[i];
        cand[i] = cand[j];
        cand[j] = tmp;
    }
    for (int i = 0; i < nc; i++) { cand[i].best = 1e18; cand[i].slice = 0; cand[i].tried = 0; }
    double T = until - now();
    if (T <= 0 || nc == 0) return;

    double p1 = now() + 0.4 * T;
    double base = 0.4 * T / (double)nc;
    if (base < 0.08) base = 0.08;
    if (base > 2.0) base = 2.0;
    for (int i = 0; i < nc && now() < p1; i++) {
        Cand *cd = &cand[i];
        if (cd->N <= bestN) continue;
        double sl = base, rem = p1 - now();
        if (sl > rem) sl = rem;
        if (sl <= 0) break;
        setup_cand(cd);
        int ok = search_group(now() + sl);
        cd->tried++;
        if (runBest < cd->best) cd->best = runBest;
        cd->slice = sl;
        if (ok) on_solve(cd);
    }

    while (now() < until) {
        int pick = -1;
        double bf = 2e18;
        for (int j = 0; j < nc; j++) {
            if (cand[j].N <= bestN) continue;
            double score = cand[j].best + 0.002 * cand[j].tried;
            if (score < bf) { bf = score; pick = j; }
        }
        if (pick < 0) break;
        Cand *cd = &cand[pick];
        double sl = cd->slice > 0 ? cd->slice * 1.7 : 0.5;
        double rem = until - now();
        if (sl > rem) sl = rem;
        if (sl <= 0.01) break;
        setup_cand(cd);
        int ok = search_group(now() + sl);
        cd->tried++;
        if (runBest < cd->best) cd->best = runBest;
        cd->slice = sl;
        if (ok) on_solve(cd);
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
    double t_end = t0 + limit * 0.92 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > MAXN - 1) hi = MAXN - 1;
    if (lo < 2 * d) lo = 2 * d;
    if (lo > hi) { printf("0 0\n"); return 0; }

    build_cands(lo, hi);
    schedule(t_end);

    if (bestN == 0) {
        printf("0 0\n");
        return 0;
    }

    setup_cand(&bestCand);
    for (int t = 0; t < d; t++) set_dart(t, bestVol[t]);
    int N = GN, V = 2 * N;
    static int adj[2 * MAXN][MAXD];
    for (int g = 0; g < N; g++)
        for (int t = 0; t < d; t++) adj[g][t] = N + fw[t][g];
    for (int y = 0; y < N; y++)
        for (int t = 0; t < d; t++) adj[N + y][t] = bw[t][y];

    /* Full check from every vertex when cheap; the group-symmetry argument covers larger graphs. */
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

    printf("%d %d\n", V, N * d);
    for (int g = 0; g < N; g++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", g, adj[g][t]);
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

    # One-orbit lifts over mixed groups; the C scheduler searches orders in [lo, hi].
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi = mb // 2
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
