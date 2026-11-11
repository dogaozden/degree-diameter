"""Semidirect-product voltage lifts with a job scheduler, for the bipartite degree-diameter problem.

Change in this version: the group family is replaced. The previous engine lifted over
F_q x| H (affine-type groups from finite fields). This version lifts over every
metacyclic group Z_m x|_r Z_k with r^k = 1 (mod m), which includes cyclic and abelian
groups. Each group is used with B in {1, 2, 3} left orbits and B right orbits.

Construction: left vertices L(i, g), right vertices R(j, g), for g in G. Dart (i, t)
with voltage x joins L(i, g) to R(tgt[i][t], g*x). Left multiplication by h is an
automorphism that maps L(i, g) to L(i, hg) and R(j, g) to R(j, hg), so it is transitive
on each orbit. BFS to depth D from the 2B orbit representatives therefore decides the
diameter of the whole graph.

Search: a single C process builds the list of (B, m, k, r) jobs whose total order
2*B*m*k lies in the window (best so far, Moore bound]. It repeatedly picks a random
untried job from the lowest totals above the current best, runs simulated annealing on
the voltages for a short slice, and records any success. A failed job is never retried.
Python checks the output with lib.is_valid and keeps a valid fallback.
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

#define MAXN 4800
#define MAXD 32
#define MAXB 3
#define MAXK 64
#define MAXJOB 120000
#define ITERS 6000

typedef struct { int total, B, m, k, r; } Job;

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

/* ------------------------------------------------------------ group Z_m x|_r Z_k
 * Element (a, b) is coded a*k + b.  (a,b)(c,e) = (a + r^b c, b + e).
 * Inverse of (a,b) is (-r^{-b} a, -b).  Requires r^k = 1 (mod m). */

static int GM, GK, GN;
static int PWR[MAXK];

static void setup_group(int m, int k, int r) {
    GM = m;
    GK = k;
    GN = m * k;
    PWR[0] = 1 % m;
    for (int b = 1; b < k; b++) PWR[b] = (int)((long)PWR[b - 1] * r % m);
}

static inline int gmul(int x, int y) {
    int a = x / GK, b = x % GK, c = y / GK, e = y % GK;
    int na = (int)(((long)PWR[b] * c + a) % GM);
    int nb = (b + e) % GK;
    return na * GK + nb;
}

static inline int ginv(int x) {
    int a = x / GK, b = x % GK;
    int nb = (GK - b) % GK;
    int t = (int)((long)PWR[nb] * a % GM);
    int na = (GM - t) % GM;
    return na * GK + nb;
}

/* ------------------------------------------------------------ multi-orbit lift state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;

static int bestTotal = 0, bestB = 0, bestM = 0, bestK = 0, bestR = 0;
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];
static int found = 0;

static int base_connected(int B) {
    int seenL[MAXB], seenR[MAXB];
    for (int i = 0; i < B; i++) { seenL[i] = 0; seenR[i] = 0; }
    seenL[0] = 1;
    int changed = 1;
    while (changed) {
        changed = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int j = tgt[i][t];
                if (seenL[i] && !seenR[j]) { seenR[j] = 1; changed = 1; }
                if (seenR[j] && !seenL[i]) { seenL[i] = 1; changed = 1; }
            }
    }
    for (int i = 0; i < B; i++)
        if (!seenL[i] || !seenR[i]) return 0;
    return 1;
}

static int set_incidence(int B) {
    int cnt[MAXB];
    for (int j = 0; j < B; j++) cnt[j] = 0;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int j = tgt[i][t];
            if (j < 0 || j >= B || cnt[j] >= d) return 0;
            incI[j][cnt[j]] = i;
            incT[j][cnt[j]] = t;
            cnt[j]++;
        }
    for (int j = 0; j < B; j++)
        if (cnt[j] != d) return 0;
    return 1;
}

static void random_pattern(int B) {
    for (;;) {
        for (int t = 0; t < d; t++) {
            int p[MAXB];
            for (int i = 0; i < B; i++) p[i] = i;
            for (int i = B - 1; i > 0; i--) {
                int r = rndint(i + 1);
                int tmp = p[i]; p[i] = p[r]; p[r] = tmp;
            }
            for (int i = 0; i < B; i++) tgt[i][t] = p[i];
        }
        if (base_connected(B) && set_incidence(B)) break;
    }
    curB = B;
}

/* Darts of the same (i, target) class need distinct voltages so the graph is simple. */
static int valid_value(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int simple_state(int B) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++)
            for (int t2 = 0; t2 < t; t2++)
                if (tgt[i][t2] == tgt[i][t] && vol[i][t2] == vol[i][t]) return 0;
    return 1;
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fw[i][t][g] = gmul(g, x);
        bw[i][t][g] = gmul(g, xi);
    }
}

/* BFS up to depth D from src; returns number of vertices reached. */
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

/* Unreached vertices from the 2B orbit representatives (identity of each orbit). */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Simulated annealing over voltages; each restart draws a fresh random base pattern.
 * Returns 1 with a simple cost-0 state in tgt/vol, 0 on timeout. */
static int search_group(double until, int iters) {
    int N = GN, B = curB;
    while (now() < until) {
        random_pattern(B);
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++) {
                int x, tries = 0;
                do { x = rndint(N); tries++; } while (!valid_value(i, t, x, t) && tries < 100000);
                set_dart(i, t, x);
            }
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d);
            int x, tries = 0;
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
        if (cost == 0 && simple_state(B)) return 1;
    }
    return 0;
}

/* ------------------------------------------------------------ jobs and scheduling */

static Job jobs[MAXJOB];
static int njobs = 0;
static unsigned char failed[MAXJOB];

static int cmp_job(const void *a, const void *b) {
    const Job *x = (const Job *)a, *y = (const Job *)b;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
    return 0;
}

/* All metacyclic groups Z_m x|_r Z_k (m >= 2, r^k = 1 mod m) with N = m*k in range,
 * times B in {1,2,3}, whose total 2*B*N lies in [minTotal, maxTotal]. */
static void build_jobs(int minTotal, int maxTotal) {
    int Nmin = (minTotal + 5) / 6;
    if (Nmin < 2 * d) Nmin = 2 * d;
    int Nmax = maxTotal / 2;
    if (Nmax > MAXN - 1) Nmax = MAXN - 1;
    njobs = 0;
    for (int k = 1; k < MAXK; k++) {
        int mlo = (Nmin + k - 1) / k;
        if (mlo < 2) mlo = 2;
        int mhi = Nmax / k;
        for (int m = mlo; m <= mhi; m++) {
            int N = m * k;
            if (N < Nmin || N > Nmax) continue;
            for (int r = 1; r < m; r++) {
                long x = 1 % m;
                for (int i = 0; i < k; i++) x = x * r % m;
                if (x != 1) continue;
                for (int B = 1; B <= MAXB; B++) {
                    int tot = 2 * B * N;
                    if (tot < minTotal || tot > maxTotal) continue;
                    if (njobs < MAXJOB) {
                        jobs[njobs].total = tot;
                        jobs[njobs].B = B;
                        jobs[njobs].m = m;
                        jobs[njobs].k = k;
                        jobs[njobs].r = r;
                        njobs++;
                    }
                }
            }
        }
    }
    qsort(jobs, (size_t)njobs, sizeof(Job), cmp_job);
}

static int lower_bound_total(int t) {
    int lo = 0, hi = njobs;
    while (lo < hi) {
        int mid = (lo + hi) / 2;
        if (jobs[mid].total < t) lo = mid + 1; else hi = mid;
    }
    return lo;
}

static void record_success(Job jb) {
    bestTotal = jb.total;
    bestB = jb.B;
    bestM = jb.m;
    bestK = jb.k;
    bestR = jb.r;
    for (int i = 0; i < jb.B; i++)
        for (int t = 0; t < d; t++) {
            bestTgt[i][t] = tgt[i][t];
            bestVol[i][t] = vol[i][t];
        }
    found = 1;
}

/* Probe untried jobs with the smallest totals above the best so far.
 * The window grows only when it holds no untried job. */
static void schedule(double until) {
    double span = until - now();
    double slice0 = span / 20.0;
    if (slice0 < 0.5) slice0 = 0.5;
    const int wnd0 = 40;
    int wnd = wnd0;
    while (now() < until) {
        int lo_t = bestTotal + 1;
        int a = lower_bound_total(lo_t);
        if (a >= njobs) break;
        int b = lower_bound_total(lo_t + wnd);
        int picked = -1;
        for (int tries = 0; tries < 32 && b > a; tries++) {
            int idx = a + rndint(b - a);
            if (!failed[idx]) { picked = idx; break; }
        }
        if (picked < 0)
            for (int idx = a; idx < b; idx++)
                if (!failed[idx]) { picked = idx; break; }
        if (picked < 0) {
            if (b >= njobs) break;
            wnd *= 2;
            continue;
        }
        double rem = until - now();
        double slice = slice0 < rem ? slice0 : rem;
        if (slice <= 0) break;
        Job jb = jobs[picked];
        setup_group(jb.m, jb.k, jb.r);
        curB = jb.B;
        if (search_group(now() + slice, ITERS)) {
            record_success(jb);
            wnd = wnd0;
        } else {
            failed[picked] = 1;
        }
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
    int minTotal = atoi(argv[5]);
    int maxTotal = atoi(argv[6]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (minTotal < 1) minTotal = 1;
    if (maxTotal > 2 * MAXB * (MAXN - 1)) maxTotal = 2 * MAXB * (MAXN - 1);
    if (maxTotal < minTotal) { printf("0 0\n"); return 0; }

    bestTotal = minTotal - 1;
    build_jobs(minTotal, maxTotal);
    if (njobs == 0) { printf("0 0\n"); return 0; }
    schedule(t_end);

    if (!found) { printf("0 0\n"); return 0; }

    /* Rebuild the best graph. */
    int B = bestB;
    setup_group(bestM, bestK, bestR);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) { printf("0 0\n"); return 0; }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    static int adj[2 * MAXB * MAXN][MAXD];
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

    /* Simplicity: no repeated neighbour anywhere. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adj[v][k] == adj[v][l]) { printf("0 0\n"); return 0; }

    /* Full BFS check from every vertex when cheap; the orbit argument covers the rest. */
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

    # Semidirect-product voltage lifts over Z_m x|_r Z_k with B = 1, 2, 3 orbits per side.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Leave room for the one-time C compile and the Python checks.
        budget = 0.82 * time_limit - (time.monotonic() - t0) - 3.0
        if budget > 4.0 and best[0] + 1 <= mb:
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2), best[0] + 1, mb],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
