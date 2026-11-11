"""Combined multi-orbit affine lifts with iterated annealing for the bipartite degree-diameter problem.

Merges two parents:
- Multi-orbit lifts (B in {1, 2, 3} orbits per side, random slot permutations, 2B BFS
  representatives decide the diameter) from g006-c09.
- Iterated annealing from the incumbent (perturb two voltages, anneal at a lower start
  temperature) from g006-c31, with periodic random restarts of the base pattern.

Search order: binary search over B = 3 candidates first, then an ascending sweep over all
(B, q, c) candidates whose order 2*B*N exceeds the best total found so far. The sweep
targets orders just above the incumbent, so it aims to beat the record rather than match it.
Python keeps a valid fallback and checks every returned graph with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Combined multi-orbit affine lift search over G = F_q x| H, B in {1,2,3} orbits.
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

#define MAXQ 257
#define MAXC 256
#define MAXN 8192
#define MAXD 32
#define MAXB 3
#define MAXCAND 4096

typedef struct { int q, p, k, c, N, B, total; } Cand;

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

/* ------------------------------------------------------------ group G = F_q x| H */

static int GQ, GC, GN;
static int Hel[MAXC], hidx[MAXQ], HM[MAXC * MAXC], PWG[MAXQ];

/* Element (a, h_j) is coded as a*c + j, h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
    GQ = q;
    GC = c;
    GN = q * c;
    int g = -1;
    for (int g0 = 2; g0< q && g < 0; g0++) {
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

static inline int gmul(int x, int y) {
    int a = x / GC, j = x % GC, b = y / GC, t = y % GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x % GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ multi-orbit state */

static int curB;
static int tgt[MAXB][MAXD], vol[MAXB][MAXD];
static int incTgt[MAXB][MAXD], incVol[MAXB][MAXD];
static int bestTgt[MAXB][MAXD], bestVol[MAXB][MAXD];
static int fw[MAXB][MAXD][MAXN], bw[MAXB][MAXD][MAXN];
static int incI[MAXB][MAXD], incT[MAXB][MAXD];
static int vis[2 * MAXB * MAXN], que[2 * MAXB * MAXN];
static int stamp_ = 0;
static int adjOut[2 * MAXB * MAXN][MAXD];

static Cand cand[MAXCAND];
static int nc = 0;
static Cand bestCand;
static int bestTotal = 0;

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

/* Each dart slot t gets a random permutation of the B orbits. */
static void random_pattern(int B) {
    curB = B;
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
}

/* Darts of the same (orbit, target) class need distinct voltages: check slots t2 < limit. */
static int ok_vol(int i, int t, int x, int limit) {
    for (int t2 = 0; t2 < limit; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int find_vol(int i, int t, int limit, int maxtries, int *out) {
    for (int tr = 0; tr < maxtries; tr++) {
        int x = rndint(GN);
        if (ok_vol(i, t, x, limit)) { *out = x; return 1; }
    }
    return 0;
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

/* Vertices: left (i, g) = i*N + g; right (j, x) = BN + j*N + x. */
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

/* Unreached vertices from the 2B orbit representatives (vertex-transitive on each side). */
static long cover_cost(void) {
    int N = GN, V = 2 * curB * N;
    long cost = 0;
    for (int i = 0; i < curB; i++) cost += (long)(V - bfs_count(i * N));
    for (int j = 0; j < curB; j++) cost += (long)(V - bfs_count((curB + j) * N));
    return cost;
}

/* Iterated annealing: fresh random pattern and voltages, then rounds that restore the
 * incumbent, perturb two voltages and anneal at a lower start temperature. After 6 stale
 * rounds the base pattern is redrawn. Returns 1 on a simple cost-0 state, 0 on timeout. */
static int search_group(int B, double until) {
    int N = GN;
    const int iters = 8000;
    int have = 0, stale = 0;
    long incCost = 0;
    curB = B;
    while (now() < until) {
        int fresh = 0;
        if (!have || stale >= 6) {
            random_pattern(B);
            for (int i = 0; i < B; i++)
                for (int t = 0; t < d; t++) {
                    int x = 0;
                    if (!find_vol(i, t, t, 100000, &x)) x = rndint(N);
                    set_dart(i, t, x);
                }
            fresh = 1;
            have = 0;
            stale = 0;
        } else {
            for (int i = 0; i < B; i++)
                for (int t = 0; t < d; t++) tgt[i][t] = incTgt[i][t];
            if (!set_incidence(B)) return 0;
            for (int i = 0; i < B; i++)
                for (int t = 0; t < d; t++) set_dart(i, t, incVol[i][t]);
            for (int r = 0; r < 2; r++) {
                int i = rndint(B), t = rndint(d), x = 0;
                if (find_vol(i, t, d, 1000, &x)) set_dart(i, t, x);
            }
        }

        long cost = cover_cost();
        if (cost == 0 && simple_state(B)) return 1;
        double c0 = (double)cost;
        double Ts = (fresh ? 0.05 : 0.02) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int i = rndint(B), t = rndint(d), x = 0;
            if (!find_vol(i, t, d, 1000, &x)) continue;
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
        if (!have || cost < incCost) {
            have = 1;
            incCost = cost;
            stale = 0;
            memcpy(incTgt, tgt, sizeof tgt);
            memcpy(incVol, vol, sizeof vol);
        } else {
            stale++;
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and phases */

static int cmp_total(const void *a, const void *b) {
    const Cand *x = a, *y = b;
    if (x->total != y->total) return x->total < y->total ? -1 : 1;
    if (x->B != y->B) return x->B - y->B;
    return x->N - y->N;
}

static void add_cands(int B, int lo, int hi) {
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N, B, 2 * B * (int)N};
                cand[nc++] = cd;
            }
        }
    }
}

static void record(const Cand *cd) {
    if (cd->total <= bestTotal) return;
    bestTotal = cd->total;
    bestCand = *cd;
    memcpy(bestTgt, tgt, sizeof tgt);
    memcpy(bestVol, vol, sizeof vol);
}

static int attempt(int ci, double slice) {
    Cand cd = cand[ci];
    double until = now() + slice;
    if (until > t_end) until = t_end;
    setup_group(cd.q, cd.p, cd.k, cd.c);
    if (search_group(cd.B, until)) {
        record(&cd);
        return 1;
    }
    return 0;
}

/* Binary search over B = 3 candidates (sorted by N, i.e. by total). */
static void phase_bsearch(double until) {
    static int b3[MAXCAND];
    int m = 0;
    for (int i = 0; i < nc; i++)
        if (cand[i].B == 3) b3[m++] = i;
    int a = 0, b = m - 1;
    while (a <= b && now() < until) {
        int mid = (a + b) / 2;
        int ci = b3[mid];
        if (cand[ci].total <= bestTotal) { a = mid + 1; continue; }
        double rem = until - now();
        double slice = 0.25 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (attempt(ci, slice)) a = mid + 1;
        else b = mid - 1;
    }
}

/* Ascending sweep over all B and (q, c) with total above the incumbent. */
static void phase_sweep(void) {
    int fails = 0;
    for (int ci = 0; ci < nc; ci++) {
        if (cand[ci].total <= bestTotal) continue;
        double rem = t_end - now();
        if (rem < 0.5 || fails >= 6) break;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        if (attempt(ci, slice)) fails = 0;
        else fails++;
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
    int lo1 = atoi(argv[5]), hi1 = atoi(argv[6]);
    int lo2 = atoi(argv[7]), hi2 = atoi(argv[8]);
    int lo3 = atoi(argv[9]), hi3 = atoi(argv[10]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi1 > MAXN - 1) hi1 = MAXN - 1;
    if (hi2 > MAXN - 1) hi2 = MAXN - 1;
    if (hi3 > MAXN - 1) hi3 = MAXN - 1;
    if (lo1 < 2 * d) lo1 = 2 * d;
    if (lo2 < 2 * d) lo2 = 2 * d;
    if (lo3 < 2 * d) lo3 = 2 * d;

    nc = 0;
    add_cands(1, lo1, hi1);
    add_cands(2, lo2, hi2);
    add_cands(3, lo3, hi3);
    if (nc == 0) { printf("0 0\n"); return 0; }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_total);

    double span = t_end - t0;
    phase_bsearch(t0 + 0.4 * span);
    phase_sweep();

    if (bestTotal == 0) { printf("0 0\n"); return 0; }

    /* Rebuild the best graph. */
    Cand bc = bestCand;
    int B = bc.B;
    setup_group(bc.q, bc.p, bc.k, bc.c);
    curB = B;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) tgt[i][t] = bestTgt[i][t];
    if (!set_incidence(B)) { printf("0 0\n"); return 0; }
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);

    int N = GN, BN = B * N, V = 2 * BN, E = BN * d;
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) adjOut[v][t] = BN + tgt[i][t] * N + fw[i][t][g];
    }
    for (int w = BN; w < V; w++) {
        int j = (w - BN) / N, x = (w - BN) % N;
        for (int k = 0; k < d; k++) {
            int i = incI[j][k], t = incT[j][k];
            adjOut[w][k] = i * N + bw[i][t][x];
        }
    }

    /* Simplicity: no repeated neighbour anywhere. */
    for (int v = 0; v < V; v++)
        for (int k = 0; k < d; k++)
            for (int l = 0; l < k; l++)
                if (adjOut[v][k] == adjOut[v][l]) { printf("0 0\n"); return 0; }

    /* Full BFS check from every vertex when cheap. */
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
                        int u = adjOut[v][k];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
            if (tail != V) { printf("0 0\n"); return 0; }
        }
    }

    printf("%d %d\n", V, E);
    for (int v = 0; v < BN; v++)
        for (int t = 0; t < d; t++)
            printf("%d %d\n", v, adjOut[v][t]);
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

    # Multi-orbit affine lifts: B = 1 (2N), B = 2 (4N), B = 3 (6N), all above the incumbent.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.85 * time_limit - (time.monotonic() - t0) - 3.0
        n0 = best[0]
        lo1 = max(2 * d, n0 // 2 + 1, mb // 8)
        hi1 = mb // 2
        lo2 = max(2 * d, n0 // 4 + 1, mb // 16)
        hi2 = mb // 4
        lo3 = max(2 * d, n0 // 6 + 1, mb // 24)
        hi3 = mb // 6
        if budget > 4.0 and (lo1 <= hi1 or lo2 <= hi2 or lo3 <= hi3):
            try:
                text = lib.run_c(C_SOURCE,
                                 [d, D, seed, round(budget, 2),
                                  lo1, hi1, lo2, hi2, lo3, hi3],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    return best
