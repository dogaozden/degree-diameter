"""Multi-block voltage lifts over affine groups for the bipartite degree-diameter problem.

Change from the parent: the parent searches only Haar graphs (one base block per side).
This version searches lifts of a base graph with K blocks per side, K = 1, 2, 3. The base
is a d-regular bipartite multigraph, written as d perfect matchings (layers) between the
A-blocks and B-blocks, and each matched pair carries a voltage in G = F_q x| H. The lift
has 2*K*|G| vertices and is d-regular. Left translations by G are automorphisms, so the
diameter check needs only 2K BFS runs, one from the identity of each block. Parallel
darts are penalised. Stage 1 searches K = 2..3 with most of the budget. Stage 2 searches
the plain Haar case K = 1, which is the parent's family, so the parent's result remains
reachable. Every result is checked with lib.is_valid before it is kept.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Multi-block voltage lift search over F_q x| H.
 * Usage: prog d D seed time_limit lo hi kmin kmax     (stdin ignored)
 * lo, hi bound the total vertex count 2*K*|G|.
 * Output: "n m" then m lines "u v" for the largest valid graph found, or "0 0".
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
#define MAXN 4096
#define MAXD 32
#define MAXK 4
#define MAXV (2 * MAXK * MAXN)
#define MAXCAND 32768

typedef struct { int q, p, fk, c, k, N, total; } Cand;

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

/* Element (a, h_j) is coded as a*c + j, with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). c = 1 gives F_q itself. */
static void setup_group(int q, int p, int fk, int c) {
    build_field(q, p, fk);
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
    int a = x / GC, j = x - a * GC;
    int b = y / GC, t = y - b * GC;
    int na = ADDT[a][MULT[Hel[j]][b]];
    return na * GC + HM[j * GC + t];
}

static int ginv(int x) {
    int a = x / GC, j = x - a * GC;
    int jn = (GC - j) % GC;
    int na = NEGT[MULT[Hel[jn]][a]];
    return na * GC + jn;
}

/* ------------------------------------------------------------ multi-block lift state */

/* Blocks: A_i = i (0..K-1), B_j = K + j. Vertex id = block*N + group element.
 * Layer t is a perfect matching between A-blocks and B-blocks: A_i is matched to
 * B_{perm[t][i]} with voltage sv[t][i]. Edge (A_i, g) ~ (B_j, g*s) for j = perm[t][i].
 * Summing the d layers gives a d-regular bipartite graph. */
static int K, N;
static int perm[MAXD][MAXK], pinv[MAXD][MAXK], sv[MAXD][MAXK];
static int fw[MAXD][MAXK][MAXN];   /* absolute id of neighbour of (A_i, g) in layer t */
static int bw[MAXD][MAXK][MAXN];   /* absolute id of neighbour of (B_j, h) in layer t */

static void rebuild_layer(int t) {
    int sinvv[MAXK];
    for (int i = 0; i < K; i++) sinvv[i] = ginv(sv[t][i]);
    for (int i = 0; i < K; i++) {
        int s = sv[t][i];
        int base = (K + perm[t][i]) * N;
        for (int g = 0; g < N; g++) fw[t][i][g] = base + gmul(g, s);
    }
    for (int j = 0; j < K; j++) {
        int i = pinv[t][j];
        int si = sinvv[i];
        int base = i * N;
        for (int h = 0; h < N; h++) bw[t][j][h] = base + gmul(h, si);
    }
}

static void rebuild_all(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) pinv[t][perm[t][i]] = i;
        rebuild_layer(t);
    }
}

static void random_state(void) {
    for (int t = 0; t < d; t++) {
        for (int i = 0; i < K; i++) perm[t][i] = i;
        for (int i = K - 1; i > 0; i--) {
            int r = rndint(i + 1);
            int tmp = perm[t][i];
            perm[t][i] = perm[t][r];
            perm[t][r] = tmp;
        }
        for (int i = 0; i < K; i++) sv[t][i] = rndint(N);
    }
}

static int stamp_ = 0;
static int vis[MAXV], que[MAXV];

/* Number of vertices within distance D of src. */
static int bfs_reach(int src) {
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            int blk = v / N;
            int e = v - blk * N;
            if (blk < K) {
                for (int t = 0; t < d; t++) {
                    int u = fw[t][blk][e];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            } else {
                int j = blk - K;
                for (int t = 0; t < d; t++) {
                    int u = bw[t][j][e];
                    if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                }
            }
        }
    }
    return tail;
}

/* Number of pairs of layers that create a parallel dart (same block pair, same voltage). */
static int dup_count(void) {
    int c = 0;
    for (int i = 0; i < K; i++)
        for (int t = 0; t < d; t++)
            for (int u = t + 1; u < d; u++)
                if (perm[t][i] == perm[u][i] && sv[t][i] == sv[u][i]) c++;
    return c;
}

/* Vertex-transitivity inside each block: one BFS per block identity decides the diameter.
 * Cost = uncovered pairs from the 2K sources, plus a heavy penalty per parallel dart. */
static long cover_cost(void) {
    int V = 2 * K * N;
    long c = 0;
    for (int b = 0; b < 2 * K; b++) c += (long)(V - bfs_reach(b * N));
    return c + 1000L * (long)dup_count();
}

static void swap_perm(int t, int i, int i2) {
    int tmp = perm[t][i];
    perm[t][i] = perm[t][i2];
    perm[t][i2] = tmp;
    pinv[t][perm[t][i]] = i;
    pinv[t][perm[t][i2]] = i2;
    rebuild_layer(t);
}

/* One random move: swap two targets in a layer (kind 1) or change one voltage (kind 0). */
static void do_random_move(int *kind, int *t, int *i, int *i2, int *old) {
    *t = rndint(d);
    if (K >= 2 && rndint(4) == 0) {
        *kind = 1;
        *i = rndint(K);
        do { *i2 = rndint(K); } while (*i2 == *i);
        swap_perm(*t, *i, *i2);
    } else {
        *kind = 0;
        *i = rndint(K);
        *i2 = 0;
        *old = sv[*t][*i];
        int x;
        do { x = rndint(N); } while (x == *old);
        sv[*t][*i] = x;
        rebuild_layer(*t);
    }
}

static void undo_move(int kind, int t, int i, int i2, int old) {
    if (kind == 1) {
        swap_perm(t, i, i2);
    } else {
        sv[t][i] = old;
        rebuild_layer(t);
    }
}

/* Iterated annealing over the layer structure and voltages.
 * The first round starts from a random state. Later rounds perturb the incumbent
 * with three random moves at a lower starting temperature.
 * Returns 1 on cost 0 (state left in the globals), 0 on timeout. */
static int search_block(double until) {
    const int iters = 4000;
    int have = 0;
    long bestc = 0;
    static int incP[MAXD][MAXK], incV[MAXD][MAXK];
    while (now() < until) {
        if (!have) {
            random_state();
        } else {
            memcpy(perm, incP, sizeof(perm));
            memcpy(sv, incV, sizeof(sv));
        }
        rebuild_all();
        if (have) {
            for (int r = 0; r < 3; r++) {
                int kd, t, i, i2, old;
                do_random_move(&kd, &t, &i, &i2, &old);
            }
        }
        long cost = cover_cost();
        if (cost == 0) return 1;
        double c0 = (double)cost;
        double Ts = (have ? 0.02 : 0.05) * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 7) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int kd, t, i, i2, old;
            do_random_move(&kd, &t, &i, &i2, &old);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                undo_move(kd, t, i, i2, old);
            }
        }
        if (cost == 0) return 1;
        if (!have || cost < bestc) {
            have = 1;
            bestc = cost;
            memcpy(incP, perm, sizeof(perm));
            memcpy(incV, sv, sizeof(sv));
        }
    }
    return 0;
}

static void print_result(void) {
    long E = (long)d * K * N;
    printf("%d %ld\n", 2 * K * N, E);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < N; g++)
            for (int t = 0; t < d; t++)
                printf("%d %d\n", i * N + g, fw[t][i][g]);
}

/* ------------------------------------------------------------ main */

static Cand cand[MAXCAND];

int main(int argc, char **argv) {
    if (argc < 9) {
        printf("0 0\n");
        return 0;
    }
    d = atoi(argv[1]);
    D = atoi(argv[2]);
    long seed = atol(argv[3]);
    double limit = atof(argv[4]);
    long lo = atol(argv[5]), hi = atol(argv[6]);
    int kmin = atoi(argv[7]), kmax = atoi(argv[8]);
    double t0 = now();
    t_end = t0 + limit * 0.9 - 0.5;
    rs ^= (uint64_t)(seed + 1) * 0x9E3779B97F4A7C15ULL;
    if (!rs) rs = 1;
    for (int i = 0; i < 10; i++) rnd();

    if (d < 2 || d > MAXD || D < 3) { printf("0 0\n"); return 0; }
    if (kmin < 1) kmin = 1;
    if (kmax > MAXK - 1) kmax = MAXK - 1;

    int nc = 0;
    for (int k = kmin; k <= kmax; k++) {
        for (int q = 3; q < MAXQ; q++) {
            int p, fk;
            if (!factor_pp(q, &p, &fk)) continue;
            for (int c = 1; c <= q - 1; c++) {
                if ((q - 1) % c) continue;
                long Nn = (long)q * c;
                if (Nn > MAXN) continue;
                long tot = 2L * k * Nn;
                if (tot < lo || tot > hi) continue;
                if (nc < MAXCAND) {
                    cand[nc].q = q;
                    cand[nc].p = p;
                    cand[nc].fk = fk;
                    cand[nc].c = c;
                    cand[nc].k = k;
                    cand[nc].N = (int)Nn;
                    cand[nc].total = (int)tot;
                    nc++;
                }
            }
        }
    }
    for (int i = 1; i < nc; i++) {
        Cand t = cand[i];
        int j = i - 1;
        while (j >= 0 && cand[j].total > t.total) { cand[j + 1] = cand[j]; j--; }
        cand[j + 1] = t;
    }

    int bestT = 0, bq = 0, bp = 0, bfk = 0, bc = 0, bK = 0;
    static int bestP[MAXD][MAXK], bestV[MAXD][MAXK];
    for (int ci = 0; ci < nc; ci++) {
        double rem = t_end - now();
        if (rem < 0.3) break;
        Cand cd = cand[ci];
        if (cd.total <= bestT) continue;
        double slice = 0.2 * rem;
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        setup_group(cd.q, cd.p, cd.fk, cd.c);
        K = cd.k;
        N = GN;
        if (search_block(now() + slice)) {
            bestT = cd.total;
            bq = cd.q;
            bp = cd.p;
            bfk = cd.fk;
            bc = cd.c;
            bK = cd.k;
            memcpy(bestP, perm, sizeof(perm));
            memcpy(bestV, sv, sizeof(sv));
        }
    }

    if (bestT == 0) {
        printf("0 0\n");
        return 0;
    }
    setup_group(bq, bp, bfk, bc);
    K = bK;
    N = GN;
    memcpy(perm, bestP, sizeof(perm));
    memcpy(sv, bestV, sizeof(sv));
    rebuild_all();
    if (cover_cost() != 0) {
        printf("0 0\n");
        return 0;
    }
    print_result();
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


def _run_c(d, D, seed, budget, lo, hi, kmin, kmax, consider):
    """One C search stage; any failure keeps the graphs already found."""
    try:
        text = lib.run_c(C_SOURCE, [d, D, seed, round(budget, 2), lo, hi, kmin, kmax],
                         stdin_graph=None, timeout=budget + 8.0)
        consider(lib.parse_graph_text(text))
    except Exception:
        pass


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

    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        # Stage 1: multi-block lifts (K = 2, 3) get about 60% of the search budget.
        total = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        b1 = 0.6 * total
        lo = max(best[0] + 2, mb // 4)
        hi = (2 * mb) // 5
        if b1 > 2.0 and lo <= hi:
            _run_c(d, D, seed, b1, lo, hi, 2, 3, consider)

        # Stage 2: plain Haar lifts (K = 1, the parent's family) use the remaining time.
        b2 = 0.85 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 2, mb // 4)
        hi = (2 * mb) // 3
        if b2 > 2.0 and lo <= hi:
            _run_c(d, D, seed + 1, b2, lo, hi, 1, 1, consider)

    if not lib.is_valid(best[0], best[1], d, D):
        best = lib.haar_graph(d, range(d))
    return best
