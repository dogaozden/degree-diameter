"""Two-class affine voltage lifts for the bipartite degree-diameter problem.

New family: the base graph has K vertices on each side (K = 1 or 2). The group is the
affine group G = F_q x| H, with |G| = N = q*c and c | q-1 (c = 1 allowed). Left
vertices are A_{i,g} and right vertices are B_{j,h}. Each base pair (i, j) carries a
voltage set S_ij, and A_{i,g} ~ B_{j,g*s} for s in S_ij.

For K = 2 the degree split is regular: |S_00| = a, |S_01| = |S_10| = d-a, |S_11| = a,
with 1 <= a <= d-1. The total order is 4N, which is a different family from the Haar
graphs (K = 1, order 2N). Both families are searched in one candidate list sorted by
vertex count, so a binary search can move between them.

Diameter check: left multiplication by G maps edges to edges and preserves the sides
and the classes i and j. So every pair of vertices is equivalent to a pair with one
endpoint in {A_{0,e}, A_{1,e}, B_{0,e}, B_{1,e}}. Four BFS runs decide the diameter.

Python keeps the projective-plane, Araujo-Lopez and W(q) baselines and the K_{d,d}
fallback. Every returned graph is checked with lib.is_valid.
"""
import itertools
import time

import lib

C_SOURCE = r'''
/* Two-class affine voltage lift search.
 * Usage: prog d D seed time_limit lo hi     (stdin ignored)
 * lo, hi bound the VERTEX COUNT of the output.
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
#define MAXN 4800
#define MAXD 32
#define MAXCAND 8192
#define MAXV 20000

typedef struct { int K, q, p, k, c, N, V; } Cand;

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

/* Element (a, h_j) is coded a*c + j with h_j = g^(j*(q-1)/c).
 * Product: (a, h_j)(b, h_t) = (a + h_j*b, h_j*h_t). */
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

/* ------------------------------------------------------------ two-class lift state
 * Pair index p = i*2 + j (i = left class, j = right class). Only pairs with SZ > 0 are used.
 * Left vertex A_{i,g} = i*N + g; right vertex B_{j,h} = K*N + j*N + h.
 * A_{i,g} ~ B_{j, g*s} for s in S_p; B_{j,h} ~ A_{i, h*s^-1}. */

static int K = 1;
static int A2 = 1;
static int SZ[4];
static int SET[4][MAXD];
static int fwd[4][MAXD][MAXN], bwd[4][MAXD][MAXN];
static int vis[MAXV], que[MAXV];
static int stamp_ = 0;

static void set_elem(int p, int t, int x) {
    SET[p][t] = x;
    int xi = ginv(x);
    for (int g = 0; g < GN; g++) {
        fwd[p][t][g] = gmul(g, x);
        bwd[p][t][g] = gmul(g, xi);
    }
}

static int in_set(int p, int x, int upto) {
    for (int i = 0; i < upto; i++)
        if (SET[p][i] == x) return 1;
    return 0;
}

static void set_sizes(void) {
    for (int p = 0; p < 4; p++) SZ[p] = 0;
    if (K == 1) {
        SZ[0] = d;
    } else {
        SZ[0] = A2;
        SZ[1] = d - A2;
        SZ[2] = d - A2;
        SZ[3] = A2;
    }
}

static void random_init(void) {
    int N = GN;
    for (int p = 0; p < 4; p++)
        for (int t = 0; t < SZ[p]; t++) {
            int x;
            do { x = rndint(N); } while (in_set(p, x, t));
            set_elem(p, t, x);
        }
}

static int pick_pair(void) {
    int act[4], na = 0;
    for (int p = 0; p < 4; p++)
        if (SZ[p] > 0) act[na++] = p;
    return act[rndint(na)];
}

/* BFS: number of vertices within distance D of src. */
static int bfs_count(int src) {
    int N = GN, KN = K * N;
    stamp_++;
    int head = 0, tail = 0;
    que[tail++] = src;
    vis[src] = stamp_;
    for (int lvl = 0; lvl < D && head < tail; lvl++) {
        int end = tail;
        while (head < end) {
            int v = que[head++];
            if (v < KN) {
                int i = v / N, g = v % N;
                for (int j = 0; j < K; j++) {
                    int p = i * 2 + j;
                    for (int t = 0; t < SZ[p]; t++) {
                        int u = KN + j * N + fwd[p][t][g];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            } else {
                int w = v - KN;
                int j = w / N, h = w % N;
                for (int i = 0; i < K; i++) {
                    int p = i * 2 + j;
                    for (int t = 0; t < SZ[p]; t++) {
                        int u = i * N + bwd[p][t][h];
                        if (vis[u] != stamp_) { vis[u] = stamp_; que[tail++] = u; }
                    }
                }
            }
        }
    }
    return tail;
}

/* Left translations are automorphisms preserving each class (i, j), so the four
 * vertices A_{i,e}, B_{j,e} represent every orbit. Their BFS covers decide diameter. */
static long cover_cost(void) {
    int N = GN, V = 2 * K * N;
    long cost = 0;
    for (int i = 0; i < K; i++) cost += V - bfs_count(i * N);
    for (int j = 0; j < K; j++) cost += V - bfs_count(K * N + j * N);
    return cost;
}

/* Simulated annealing over voltage sets (with restarts) in the current group.
 * Returns 1 when cost 0 is reached (diameter <= D), 0 on timeout. */
static int search_group(double until) {
    int N = GN;
    const int iters = 8000;
    while (now() < until) {
        if (K == 2) A2 = 1 + rndint(d - 1);
        set_sizes();
        random_init();
        long cost = cover_cost();
        double c0 = cost > 0 ? (double)cost : 1.0;
        double Ts = 0.05 * c0 + 1.0, Te = 0.3;
        for (int it = 0; it < iters && cost > 0; it++) {
            if ((it & 15) == 0 && now() > until) return 0;
            double T = Ts * pow(Te / Ts, (double)it / iters);
            int p = pick_pair();
            int t = rndint(SZ[p]);
            int x;
            do { x = rndint(N); } while (in_set(p, x, SZ[p]));
            int old = SET[p][t];
            set_elem(p, t, x);
            long c2 = cover_cost();
            if (c2 <= cost || rnd01() < exp(-(double)(c2 - cost) / T)) {
                cost = c2;
            } else {
                set_elem(p, t, old);
            }
        }
        if (cost == 0) return 1;
    }
    return 0;
}

static void print_result(void) {
    int N = GN, KN = K * N;
    printf("%d %d\n", 2 * KN, KN * d);
    for (int i = 0; i < K; i++)
        for (int g = 0; g < N; g++)
            for (int j = 0; j < K; j++) {
                int p = i * 2 + j;
                for (int t = 0; t < SZ[p]; t++)
                    printf("%d %d\n", i * N + g, KN + j * N + fwd[p][t][g]);
            }
}

/* ------------------------------------------------------------ candidates */

static int cmp_cand(const void *x, const void *y) {
    const Cand *a = x, *b = y;
    if (a->V != b->V) return a->V < b->V ? -1 : 1;
    if (a->K != b->K) return a->K - b->K;
    if (a->q != b->q) return a->q - b->q;
    return a->c - b->c;
}

static void enter_cand(const Cand *cd) {
    K = cd->K;
    setup_group(cd->q, cd->p, cd->k, cd->c);
}

static Cand cand[MAXCAND];
static int nc = 0;
static int best_idx = -1, bestV = 0;
static int bestSZ[4], bestSET[4][MAXD];

static void record_best(int idx) {
    best_idx = idx;
    bestV = cand[idx].V;
    memcpy(bestSZ, SZ, sizeof(SZ));
    memcpy(bestSET, SET, sizeof(SET));
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

    for (int q = 3; q < MAXQ; q++) {
        int p, k;
        if (!factor_pp(q, &p, &k)) continue;
        for (int c = 1; c <= q - 1; c++) {
            if ((q - 1) % c) continue;
            int N = q * c;
            if (N < d + 1 || N > MAXN) continue;
            for (int KK = 1; KK <= 2; KK++) {
                int V = 2 * KK * N;
                if (V < lo || V > hi) continue;
                if (nc < MAXCAND) {
                    Cand cd = {KK, q, p, k, c, N, V};
                    cand[nc++] = cd;
                }
            }
        }
    }
    qsort(cand, (size_t)nc, sizeof(Cand), cmp_cand);

    /* Phase 1: binary search over vertex counts. Each probe gets an equal share of
     * the remaining time, divided by the probes still needed. */
    int a = 0, b = nc - 1;
    while (a <= b && now() < t_end) {
        int mid = (a + b) / 2;
        int span = b - a + 1;
        int probes = 1;
        while (span > 1) { span = (span + 1) / 2; probes++; }
        double rem = t_end - now();
        double slice = rem / (probes + 1);
        if (slice < 1.0) slice = 1.0;
        if (slice > rem) slice = rem;
        enter_cand(&cand[mid]);
        if (search_group(now() + slice)) {
            if (cand[mid].V > bestV) record_best(mid);
            a = mid + 1;
        } else {
            b = mid - 1;
        }
    }

    /* Phase 2: spend leftover time on the next few candidates above the best. */
    int fails = 0;
    int idx = best_idx < 0 ? 0 : best_idx + 1;
    while (idx < nc && now() < t_end && fails < 2) {
        if (cand[idx].V <= bestV) { idx++; continue; }
        double rem = t_end - now();
        double slice = rem * 0.6;
        if (slice > rem) slice = rem;
        enter_cand(&cand[idx]);
        if (search_group(now() + slice)) {
            record_best(idx);
            idx++;
            fails = 0;
        } else {
            idx++;
            fails++;
        }
    }

    if (best_idx < 0) {
        printf("0 0\n");
        return 0;
    }
    enter_cand(&cand[best_idx]);
    memcpy(SZ, bestSZ, sizeof(SZ));
    for (int p = 0; p < 4; p++)
        for (int t = 0; t < SZ[p]; t++)
            set_elem(p, t, bestSET[p][t]);
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

    # Affine-group two-class lifts (orders 2N and 4N). The C search works in vertex counts.
    if d >= 2 and D >= 3:
        mb = lib.moore_bound(d, D)
        budget = 0.8 * time_limit - (time.monotonic() - t0) - 2.0
        lo = max(best[0] + 1, mb // 8)
        hi = mb
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
