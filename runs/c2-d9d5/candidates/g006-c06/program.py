"""Multi-orbit offset-base voltage lifts over semidirect groups Z_m x| Z_b.

New idea in this version: the parent's Haar graph has two vertex orbits under the
group, so every pair of orbits is joined by the same d voltage darts. Here the
base has K left orbits and K right orbits. Dart (u, i) joins left orbit u to right
orbit (u + M_i) mod K, with voltage g_{u,i} in G. The offset multiset M (size d,
entries in Z_K) gives a d-regular base for any choice of M, so the lift is d-regular
and bipartite with 2KN vertices. Left translations act on the lift, so diameter
<= D only needs BFS from one vertex in each of the 2K orbits.

The C engine enumerates semidirect groups Z_m x| Z_b with r^b = 1 mod m, for K in
{1,2,3,4,6,8,9,12,16}. It sorts candidates by total order and binary-searches for
the largest feasible one. Simulated annealing moves voltages and offsets. The
cost is the number of unreached (source, vertex) pairs plus a penalty for
duplicate darts.

Python keeps the projective-plane, Araujo-Lopez, W(q) and K_{d,d} baselines. Every
returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-orbit voltage lifts over Z_m x| Z_b.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the total vertex count 2*K*N.
 * Output: "n m" then m lines "u v", or "0 0".
 */
#define _POSIX_C_SOURCE 200809L
#include <math.h>
#include <stdint.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#define MAXG 5000
#define MAXK 16
#define MAXD 16
#define MAXV 20000
#define MAXCAND 20000

typedef struct { int m, b, r, k, N, V; } Cand;

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
static int powmod_i(int r, int e, int m) {
    long res = 1 % m, base = r % m;
    while (e > 0) {
        if (e & 1) res = res * base % m;
        base = base * base % m;
        e >>= 1;
    }
    return (int)res;
}

/* ------------------------------------------------------------ group Z_m x| Z_b
 * Element (a,j) is coded a*GB + j. Product: (a,j)(c,t) = (a + r^j c, j + t). */
static int GM, GB, GN;
static int RP[MAXG];
static int AA[MAXG], JJ[MAXG];

static void setup_group(int m, int b, int r) {
    GM = m;
    GB = b;
    GN = m * b;
    RP[0] = 1 % m;
    for (int j = 1; j < b; j++) RP[j] = (int)(((long)RP[j - 1] * r) % m);
    for (int x = 0; x < GN; x++) {
        AA[x] = x / GB;
        JJ[x] = x % GB;
    }
}

static inline int gmul(int x, int y) {
    int a = AA[x], j = JJ[x], c = AA[y], t = JJ[y];
    int na = (int)(((long)a + (long)RP[j] * c) % GM);
    int nt = j + t;
    if (nt >= GB) nt -= GB;
    return na * GB + nt;
}

static int ginv(int x) {
    int a = AA[x], j = JJ[x];
    int nj = (GB - j) % GB;
    int na = (int)((GM - ((long)RP[nj] * a) % GM) % GM);
    return na * GB + nj;
}

/* ------------------------------------------------------------ lift state
 * Left vertex (u,x) has id u*GN + x. Right vertex (w,y) has id K*GN + w*GN + y.
 * Dart (u,i): (u,x) ~ (LW[u][i], x * G[u][i]), with LW[u][i] = (u + M[i]) mod K.
 * Right (w,y) is adjacent to (u, y * H[u][i]) for each dart (u,i) entering w;
 * exactly d darts enter each right orbit.
 */
static int K;
static int M[MAXD];
static int G[MAXK][MAXD], H[MAXK][MAXD];
static int LW[MAXK][MAXD], RU[MAXK][MAXD], RI[MAXK][MAXD];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int bestG[MAXK][MAXD], bestM[MAXD];

static Cand cand[MAXCAND];
static int nc = 0;

static void refresh(void) {
    int cnt[MAXK];
    for (int w = 0; w < K; w++) cnt[w] = 0;
    for (int u = 0; u < K; u++)
        for (int i = 0; i < d; i++) {
            int w = (u + M[i]) % K;
            H[u][i] = ginv(G[u][i]);
            LW[u][i] = w;
            RU[w][cnt[w]] = u;
            RI[w][cnt[w]] = i;
            cnt[w]++;
        }
}

/* Number of vertices within distance D of src. */
static int bfs_count(int src) {
    int KN = K * GN;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int u = v / GN, x = v % GN;
                for (int i = 0; i < d; i++) {
                    int y = gmul(x, G[u][i]);
                    int t = KN + LW[u][i] * GN + y;
                    if (vis[t] != stamp_) { vis[t] = stamp_; que[tail++] = t; }
                }
            } else {
                int rr = v - KN;
                int w = rr / GN, y = rr % GN;
                for (int t = 0; t < d; t++) {
                    int u = RU[w][t], i = RI[w][t];
                    int x = gmul(y, H[u][i]);
                    int id = u * GN + x;
                    if (vis[id] != stamp_) { vis[id] = stamp_; que[tail++] = id; }
                }
            }
        }
    }
    return tail;
}

/* Cost 0 iff the lift is simple and has diameter <= D. Sources are one vertex per
 * orbit: left-translation maps any pair to one whose left endpoint is (u,e). */
static long evaluate(void) {
    refresh();
    long pen = 0;
    for (int u = 0; u < K; u++)
        for (int i = 0; i < d; i++)
            for (int j = i + 1; j < d; j++)
                if (M[i] == M[j] && G[u][i] == G[u][j]) pen++;
    int V = 2 * K * GN;
    long cost = 0;
    for (int u = 0; u < K; u++) {
        cost += V - bfs_count(u * GN);
        cost += V - bfs_count(K * GN + u * GN);
    }
    return cost + pen * (long)V;
}

/* Simulated annealing over voltages and offsets for the current group and K. */
static int search(double until) {
    const int iters = 3000;
    while (now() < until) {
        for (int i = 0; i < d; i++) M[i] = rndint(K);
        for (int u = 0; u < K; u++)
            for (int i = 0; i < d; i++) G[u][i] = rndint(GN);
        long cost = evaluate();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = 0.1 * c0 + 2.0, Te = 0.2;
        for (int it = 0; it < iters; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            if (rnd01() < 0.85) {
                int u = rndint(K), i = rndint(d);
                int old = G[u][i];
                G[u][i] = rndint(GN);
                long c2 = evaluate();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else G[u][i] = old;
            } else {
                int i = rndint(d);
                int old = M[i];
                M[i] = rndint(K);
                long c2 = evaluate();
                if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) cost = c2;
                else M[i] = old;
            }
            if (cost == 0) return 1;
        }
    }
    return 0;
}

static int probe(int idx, double until) {
    const Cand *c = &cand[idx];
    K = c->k;
    setup_group(c->m, c->b, c->r);
    if (search(until)) {
        memcpy(bestG, G, sizeof G);
        memcpy(bestM, M, sizeof M);
        return 1;
    }
    return 0;
}

static void print_result(const Cand *c) {
    K = c->k;
    setup_group(c->m, c->b, c->r);
    memcpy(G, bestG, sizeof G);
    memcpy(M, bestM, sizeof M);
    if (evaluate() != 0) {
        printf("0 0\n");
        return;
    }
    int KN = K * GN;
    printf("%d %d\n", 2 * KN, KN * d);
    for (int u = 0; u < K; u++)
        for (int x = 0; x < GN; x++)
            for (int i = 0; i < d; i++) {
                int w = LW[u][i];
                int y = gmul(x, G[u][i]);
                printf("%d %d\n", u * GN + x, KN + w * GN + y);
            }
}

static int cmpc(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->V != y->V) return x->V < y->V ? -1 : 1;
    if (x->m != y->m) return x->m - y->m;
    if (x->b != y->b) return x->b - y->b;
    return x->r - y->r;
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
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi > 2 * MAXG) hi = 2 * MAXG;
    if (hi > MAXV / 2) hi = MAXV / 2;
    if (lo < 2 * d) lo = 2 * d;
    if (lo < 2) lo = 2;
    if (hi < lo) { printf("0 0\n"); return 0; }

    /* Candidates: total order V = 2*k*m*b in [lo, hi], Z_m x| Z_b with r^b = 1 mod m. */
    static const int KS[9] = {1, 2, 3, 4, 6, 8, 9, 12, 16};
    for (int ki = 0; ki < 9; ki++) {
        int k = KS[ki];
        for (long b = 1; 2L * k * b <= hi; b++) {
            long per = 2L * k * b;
            long mlo = (lo + per - 1) / per;
            if (mlo < 1) mlo = 1;
            long mhi = hi / per;
            for (long m = mlo; m <= mhi; m++) {
                int rmax = (m > 1) ? (int)m : 1;
                for (int r = 0; r < rmax && nc < MAXCAND; r++) {
                    if (gcd_i(r, (int)m) != 1) continue;
                    if (powmod_i(r, (int)b, (int)m) != 1 % (int)m) continue;
                    Cand c;
                    c.m = (int)m;
                    c.b = (int)b;
                    c.r = r;
                    c.k = k;
                    c.N = (int)(m * b);
                    c.V = 2 * k * c.N;
                    cand[nc++] = c;
                }
            }
        }
    }
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmpc);

    /* Phase 1: binary search on the sorted order for the largest feasible candidate. */
    int a = 0, hiIdx = nc - 1, best = -1;
    while (a <= hiIdx && now() < t_end) {
        int mid = (a + hiIdx) / 2;
        double rem = t_end - now();
        double slice = rem * 0.2;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (probe(mid, now() + slice)) {
            best = mid;
            a = mid + 1;
        } else {
            hiIdx = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next candidates above the best. */
    int fails = 0;
    int idx = best + 1;
    while (idx < nc && now() < t_end && fails < 3) {
        double rem = t_end - now();
        double slice = rem * 0.5;
        if (slice > rem) slice = rem;
        if (probe(idx, now() + slice)) {
            best = idx;
            fails = 0;
        } else {
            fails++;
        }
        idx++;
    }

    if (best < 0) {
        printf("0 0\n");
        return 0;
    }
    print_result(&cand[best]);
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

    # Multi-orbit voltage lifts over semidirect groups, searched in C.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.88 * time_limit - (time.monotonic() - t0) - 3.0
        lo = max(best[0] + 2, mb // 4)
        hi = max((mb * 3) // 10, lo)
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
