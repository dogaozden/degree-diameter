"""Two-orbit affine Haar lifts with iterated annealing for the bipartite degree-diameter problem.

Combines two ideas:
  * Two-orbit lifts: the group G = F_q x| H (|G| = N = q*c) acts on each side with
    B = 2 orbits. Left orbit i sends d darts to the right orbits with pattern a:
    L0 -> R0 (a darts), L0 -> R1 (d-a), L1 -> R0 (d-a), L1 -> R1 (a). The graph has
    4N vertices. Left translations are automorphisms with 4 orbits, so BFS from one
    representative per orbit decides the diameter. A single-orbit (B = 1) Haar lift
    is searched afterwards as a fallback.
  * Iterated annealing: each cell keeps an incumbent voltage assignment. Most rounds
    perturb the incumbent (two darts replaced) and anneal from a lower start
    temperature. Some rounds restart with a new pattern a.

Orders are scanned in ascending order from the threshold that beats the current best,
so the most feasible cells are tried first. Before output, the C engine checks the
explicit graph (degree, simplicity, and diameter via BFS). Python verifies the result
with lib.is_valid and keeps a valid fallback.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-orbit (B = 2) and single-orbit (B = 1) affine voltage lifts over G = F_q x| H.
 * Usage: prog d D seed time_limit lo2 hi2 lo1 hi1
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
#define MAXV (4 * MAXN)
#define MAXCAND 16384
#define ITER_RESTART 6000
#define ITER_PERTURB 3000

typedef struct { int q, p, k, c, N; } Cand;

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

/* Element (a, h_j) is coded as a*c + j with h_j = g^(j*(q-1)/c). */
static void setup_group(int q, int p, int k, int c) {
    build_field(q, p, k);
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

/* ------------------------------------------------------------ lift state */

/* Left vertex (i,g) = i*N + g. Right vertex (j,y) = B*N + j*N + y.
 * Dart (i,t) joins L_(i,g) to R_(tgt[i][t], g*vol[i][t]). */
static int B, A;
static int tgt[2][MAXD], vol[2][MAXD];
static int incI[2][MAXD], incT[2][MAXD];
static int fwd[2][MAXD][MAXN], bwd[2][MAXD][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;
static int adjf[MAXV][MAXD], dg[MAXV];

static int bestTotal = 0, bestB, bestA, bestN, bestQ, bestP, bestK, bestC;
static int bestVol[2][MAXD];
static Cand cand[MAXCAND];
static int nc = 0;

/* B = 1: all darts to R0. B = 2: a darts L0->R0, d-a darts L0->R1, d-a darts L1->R0, a darts L1->R1. */
static void set_pattern(int b, int a) {
    B = b;
    A = a;
    for (int t = 0; t < d; t++) {
        if (B == 1) {
            tgt[0][t] = 0;
        } else {
            tgt[0][t] = (t < a) ? 0 : 1;
            tgt[1][t] = (t < a) ? 1 : 0;
        }
    }
    for (int j = 0; j < B; j++) {
        int cnt = 0;
        for (int i = 0; i < B; i++)
            for (int t = 0; t < d; t++)
                if (tgt[i][t] == j) {
                    incI[j][cnt] = i;
                    incT[j][cnt] = t;
                    cnt++;
                }
    }
}

static void set_dart(int i, int t, int x) {
    vol[i][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[i][t][g] = gmul(g, x);
        bwd[i][t][g] = gmul(g, xi);
    }
}

/* Darts of the same left orbit and target class need distinct voltages (simple graph). */
static int ok_value(int i, int t, int x) {
    for (int t2 = 0; t2 < d; t2++)
        if (t2 != t && tgt[i][t2] == tgt[i][t] && vol[i][t2] == x) return 0;
    return 1;
}

static int random_darts(void) {
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) vol[i][t] = -1;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) {
            int x = -1, tries = 0;
            do { x = rndint(GN); tries++; } while (!ok_value(i, t, x) && tries < 100000);
            if (tries >= 100000) return 0;
            set_dart(i, t, x);
        }
    return 1;
}

/* Number of vertices within distance D of src (uses the orbit structure). */
static int bfs_reach(int src) {
    int N = GN, BN = B * N;
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
                    int u = BN + tgt[i][t] * N + fwd[i][t][g];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int w = v - BN, j = w / N, y = w % N;
                for (int k = 0; k < d; k++) {
                    int i = incI[j][k], t = incT[j][k];
                    int u = i * N + bwd[i][t][y];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Unreached pairs from one representative per orbit (2B orbits, each of size N). */
static long cover_cost(void) {
    int N = GN, V = 2 * B * N;
    long cost = 0;
    for (int s = 0; s < 2 * B; s++) cost += (long)(V - bfs_reach(s * N));
    return cost;
}

/* Simulated annealing on the voltages. Returns the final cost (0 = success). */
static long anneal(double until, double ts0, int iters) {
    long cost = cover_cost();
    if (cost == 0) return 0;
    double Ts = ts0 * (double)cost + 1.0, Te = 0.3;
    for (int it = 0; it < iters && cost > 0; it++) {
        if ((it & 15) == 0 && now() > until) break;
        double T = Ts * pow(Te / Ts, (double)it / iters);
        int i = rndint(B), t = rndint(d);
        int x = 0, tries = 0;
        do { x = rndint(GN); tries++; } while (!ok_value(i, t, x) && tries < 1000);
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
    return cost;
}

/* Iterated search in one group: restarts with a random pattern, otherwise perturbs the
 * incumbent (two darts replaced) and anneals from a lower temperature.
 * Returns 1 with a cost-0 state left in (B, A, vol), 0 on timeout. */
static int search_cell(double until) {
    int have = 0, incA_ = 0;
    long bestc = 0;
    int incV[2][MAXD];
    while (now() < until) {
        if (!have || rnd01() < 0.3) {
            int a = (B == 1) ? d : 1 + rndint(d / 2);
            set_pattern(B, a);
            if (!random_darts()) continue;
            long c = anneal(until, 0.05, ITER_RESTART);
            if (c == 0) return 1;
            if (!have || c < bestc) {
                have = 1;
                bestc = c;
                incA_ = A;
                for (int i = 0; i < B; i++)
                    for (int t = 0; t < d; t++) incV[i][t] = vol[i][t];
            }
        } else {
            set_pattern(B, incA_);
            for (int i = 0; i < B; i++)
                for (int t = 0; t < d; t++) set_dart(i, t, incV[i][t]);
            for (int r = 0; r < 2; r++) {
                int i = rndint(B), t = rndint(d), x = 0, tries = 0;
                do { x = rndint(GN); tries++; } while (!ok_value(i, t, x) && tries < 1000);
                if (tries < 1000) set_dart(i, t, x);
            }
            long c = anneal(until, 0.02, ITER_PERTURB);
            if (c == 0) return 1;
            if (c < bestc) {
                bestc = c;
                incA_ = A;
                for (int i = 0; i < B; i++)
                    for (int t = 0; t < d; t++) incV[i][t] = vol[i][t];
            }
        }
    }
    return 0;
}

/* ------------------------------------------------------------ candidates and scan */

static void build_cands(int lo, int hi) {
    nc = 0;
    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 2; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            long N = (long)q * c;
            if (N < lo || N > hi) continue;
            if (nc < MAXCAND) {
                Cand cd = {q, p, k, c, (int)N};
                cand[nc++] = cd;
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].N > t.N) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }
}

static void record_state(const Cand *cd) {
    int total = 2 * B * cd->N;
    if (total <= bestTotal) return;
    bestTotal = total;
    bestB = B;
    bestA = A;
    bestN = cd->N;
    bestQ = cd->q;
    bestP = cd->p;
    bestK = cd->k;
    bestC = cd->c;
    for (int i = 0; i < B; i++)
        for (int t = 0; t < d; t++) bestVol[i][t] = vol[i][t];
}

/* Walk candidates upward from the threshold. Stop after 3 consecutive failures,
 * since feasibility is roughly monotone in the order. */
static void scan(int b, int lo, int hi, double until) {
    if (lo > hi) return;
    build_cands(lo, hi);
    int fails = 0;
    for (int ci = 0; ci < nc && fails < 3 && now() < until; ci++) {
        Cand cd = cand[ci];
        if (2 * b * cd.N <= bestTotal) continue;
        double rem = until - now();
        double slice = 0.2 * rem;
        if (slice < 2.0) slice = 2.0;
        if (slice > rem) slice = rem;
        setup_group(cd.q, cd.p, cd.k, cd.c);
        B = b;
        if (search_cell(now() + slice)) {
            record_state(&cd);
            fails = 0;
        } else {
            fails++;
        }
    }
}

/* ------------------------------------------------------------ output */

static int bfs_full(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            for (int k = 0; k < d; k++) {
                int u = adjf[v][k];
                if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
            }
        }
    }
    return tail;
}

/* Rebuild the best state. Verify it explicitly; print it only when emit is set. */
static int finish(int emit) {
    setup_group(bestQ, bestP, bestK, bestC);
    set_pattern(bestB, bestA);
    for (int i = 0; i < bestB; i++)
        for (int t = 0; t < d; t++) set_dart(i, t, bestVol[i][t]);
    int N = GN, BN = bestB * N, V = 2 * BN;
    for (int u = 0; u < V; u++) dg[u] = 0;
    for (int v = 0; v < BN; v++) {
        int i = v / N, g = v % N;
        for (int t = 0; t < d; t++) {
            int u = BN + tgt[i][t] * N + fwd[i][t][g];
            adjf[v][t] = u;
            if (dg[u] >= d) return 0;
            adjf[u][dg[u]++] = v;
        }
        dg[v] = d;
    }
    for (int u = BN; u < V; u++)
        if (dg[u] != d) return 0;
    for (int x = 0; x < V; x++)
        for (int k1 = 0; k1 < d; k1++)
            for (int k2 = k1 + 1; k2 < d; k2++)
                if (adjf[x][k1] == adjf[x][k2]) return 0;
    if (V <= 5000) {
        for (int s = 0; s < V; s++)
            if (bfs_full(s) != V) return 0;
    } else {
        for (int s = 0; s < 2 * bestB; s++)
            if (bfs_full(s * N) != V) return 0;
    }
    if (emit) {
        printf("%d %d\n", V, BN * d);
        for (int v = 0; v < BN; v++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", v, adjf[v][t]);
    }
    return 1;
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
    int lo2 = atoi(argv[5]), hi2 = atoi(argv[6]);
    int lo1 = atoi(argv[7]), hi1 = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.93 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (hi2 > MAXN) hi2 = MAXN;
    if (hi1 > MAXN) hi1 = MAXN;
    if (lo2 < 2 * d) lo2 = 2 * d;
    if (lo1 < 2 * d) lo1 = 2 * d;

    double t_mid = t0 + 0.65 * (t_end - t0);
    scan(2, lo2, hi2, t_mid);
    scan(1, lo1, hi1, t_end);

    if (bestTotal == 0) { printf("0 0\n"); return 0; }
    if (!finish(0)) { printf("0 0\n"); return 0; }
    finish(1);
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

    # Two-orbit lifts (4N vertices) need N > best/4; single-orbit lifts (2N) need N > best/2.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.90 * time_limit - (time.monotonic() - t0) - 2.0
        lo2 = max(2 * d, best[0] // 4 + 1, mb // 16)
        hi2 = mb // 4
        lo1 = max(2 * d, best[0] // 2 + 1, mb // 8)
        hi1 = mb // 2
        if budget > 2.0 and (lo2 <= hi2 or lo1 <= hi1):
            try:
                text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2),
                                            lo2, hi2, lo1, hi1],
                                 stdin_graph=None, timeout=budget + 8.0)
                consider(lib.parse_graph_text(text))
            except Exception:
                pass   # keep the valid Python graph

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
